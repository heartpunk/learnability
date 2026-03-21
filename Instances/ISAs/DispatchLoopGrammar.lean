import Instances.ISAs.DispatchLoopStabilization

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA VexIRParser

/-! ## DFA & CFG Extraction -/

/-- Strip rip-guard conjuncts from a PC, returning only the data guard. -/
def stripRipGuards {Reg : Type} [BEq Reg] (ip_reg : Reg) (pc : SymPC Reg) : SymPC Reg :=
  let cs := SymPC.conjuncts pc |>.filter fun c => match c with
    | .eq (.reg r) (.const _) => !(r == ip_reg)
    | _ => true
  match cs with
  | [] => .true
  | c :: rest => rest.foldl .and c

/-- Pretty-print a SymExpr concisely. -/
def ppExpr : SymExpr Amd64Reg → String
  | .const v =>
    let n := v.toNat
    if n ≥ 32 && n ≤ 126 then s!"'{Char.ofNat n}'"
    else s!"{n}"
  | .reg r => toString r
  | .add64 a b => s!"({ppExpr a}+{ppExpr b})"
  | .sub64 a b => s!"({ppExpr a}-{ppExpr b})"
  | .and64 a b => s!"({ppExpr a}&{ppExpr b})"
  | .or64  a b => s!"({ppExpr a}|{ppExpr b})"
  | .xor64 a b => s!"({ppExpr a}^{ppExpr b})"
  | .shr64 a b | .mul64 a b | .mul32 a b | .sar64 a b | .sar32 a b => s!"({ppExpr a}>>{ppExpr b})"
  | .shl64 a b => s!"({ppExpr a}<<{ppExpr b})"
  | .low32 e   => s!"lo32({ppExpr e})"
  | .uext32 e  => s!"zx32({ppExpr e})"
  | .sext32to64 e => s!"sx32({ppExpr e})"
  | _ => "..."

/-- Pretty-print a SymPC atom as a character condition on rax. -/
def ppCharCond (raxReg : Amd64Reg) : SymPC Amd64Reg → String
  | .eq (.reg r) (.const c) =>
    if r == raxReg then
      let n := c.toNat
      if n ≥ 32 && n ≤ 126 then s!"rax=='{Char.ofNat n}'"
      else s!"rax=={n}"
    else s!"{r}=={ppExpr (.const c)}"
  | .eq l r => s!"{ppExpr l}=={ppExpr r}"
  | .le (.const lo) (.reg r) =>
    if r == raxReg then s!"rax>={lo.toNat}" else s!"{lo.toNat}<={r}"
  | .le (.reg r) (.const hi) =>
    if r == raxReg then s!"rax<={hi.toNat}" else s!"{r}<={hi.toNat}"
  | .le l r => s!"{ppExpr l}<={ppExpr r}"
  | .lt (.const lo) (.reg r) =>
    if r == raxReg then s!"rax>{lo.toNat}" else s!"{lo.toNat}<{r}"
  | .lt (.reg r) (.const hi) =>
    if r == raxReg then s!"rax<{hi.toNat}" else s!"{r}<{hi.toNat}"
  | .lt l r => s!"{ppExpr l}<{ppExpr r}"
  | .not inner => "NOT(" ++ ppCharCond raxReg inner ++ ")"
  | .true => "true"
  | _ => "<cond>"

/-- Format a data guard PC (non-rip conjuncts) as a human-readable string. -/
def describeDataGuard (raxReg : Amd64Reg) (pc : SymPC Amd64Reg) : String :=
  let cs := SymPC.conjuncts pc
  match cs with
  | [.true] => "*"
  | _ => " & ".intercalate (cs.map (ppCharCond raxReg))

/-- Format a UInt64 as a hex address. -/
def hexAddr (a : UInt64) : String :=
  s!"0x{String.ofList (Nat.toDigits 16 a.toNat)}"

/-- Print DFA transition table from next_sym body branches (single-step transitions). -/
def printDFATable (log : String → IO Unit)
    (bodyArr : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg))) : IO Unit := do
  let ip_reg := Amd64Reg.rip
  let rax_reg := Amd64Reg.rax
  let mut trans : Array (UInt64 × SymPC Amd64Reg × UInt64) := #[]
  for b in bodyArr do
    match extractRipGuard ip_reg b.pc, extractRipTarget ip_reg b.sub with
    | some src, some tgt =>
      trans := trans.push (src, stripRipGuards ip_reg b.pc, tgt)
    | _, _ => pure ()
  log s!"\n=== DFA Transition Table (next_sym, {trans.size} single-step transitions) ==="
  let mut bySource : Std.HashMap UInt64 (Array (SymPC Amd64Reg × UInt64)) := {}
  let mut allStates : Std.HashSet UInt64 := {}
  for (src, guard, tgt) in trans do
    let arr := bySource.getD src #[]
    bySource := bySource.insert src (arr.push (guard, tgt))
    allStates := allStates.insert src
    allStates := allStates.insert tgt
  log s!"  States: {allStates.size}, Source states: {bySource.size}"
  for (src, edges) in bySource.toArray do
    log s!"  State {hexAddr src}:"
    for (guard, tgt) in edges do
      log s!"    [{describeDataGuard rax_reg guard}] -> {hexAddr tgt}"

/-! ## Production Extraction via Body CFG -/

/-- Check if a SymExpr references the rsp register (for detecting call return-address stores). -/
def exprUsesRSP : SymExpr Amd64Reg → Bool
  | .reg .rsp => true
  | .add64 a b | .sub64 a b => exprUsesRSP a || exprUsesRSP b
  | .load _ _ addr => exprUsesRSP addr
  | _ => false

/-- Extract the constant return address pushed by a call instruction at [rsp - k]. -/
def extractCallReturn (mem : SymMem Amd64Reg) : Option UInt64 :=
  match mem with
  | .base => none
  | .store _ inner addr (.const v) =>
    if exprUsesRSP addr then some v else extractCallReturn inner
  | .store _ inner _ _ => extractCallReturn inner

/-- Strip sign-extension / low-extract wrappers and +offset to reach a raw constant.
    Used to decode the character constants inside VEX-style signed-comparison expressions
    (e.g. sx32(lo32(lo32(const '/')))+2^63  →  '/').
    Returns Some v only if v is a printable ASCII char (32..126). -/
def stripToCharConst : SymExpr Amd64Reg → Option UInt64
  | .const v => if v.toNat ≥ 32 && v.toNat ≤ 126 then some v else none
  | .low32 inner | .uext32 inner | .sext32to64 inner => stripToCharConst inner
  | .add64 a b => stripToCharConst a <|> stripToCharConst b
  | _ => none

/-- Try to extract a printable ASCII character from an expression (even if wrapped). -/
def extractCharConstFromExpr (e : SymExpr Amd64Reg) : Option Char :=
  (stripToCharConst e).bind fun v =>
    let n := v.toNat
    if n ≥ 32 && n ≤ 126 then some (Char.ofNat n) else none

/-- Describe the expected token at a next_sym call site, given the data guard PC.
    Extracts character constants and infers token class (id, int, or specific char). -/
def describeCallSiteToken (guard : SymPC Amd64Reg) : String :=
  let cs := SymPC.conjuncts guard
  if cs == [.true] then "token"
  else
    -- Priority 1: exact equality (specific character)
    let eqChar := cs.findSome? fun c => match c with
      | .eq l r => extractCharConstFromExpr l <|> extractCharConstFromExpr r
      | _ => none
    match eqChar with
    | some ch => s!"'{ch}'"
    | none =>
      -- Priority 2: range check → infer digit / letter class
      let loBounds := cs.filterMap fun c => match c with
        | .le l _ | .lt l _ => extractCharConstFromExpr l
        | _ => none
      let hiBounds := cs.filterMap fun c => match c with
        | .le _ r | .lt _ r => extractCharConstFromExpr r
        | _ => none
      match loBounds, hiBounds with
      | lo :: _, hi :: _ =>
        if lo == '/' || lo == '0' then "int"
        else if lo == '`' || lo == 'a' then "id"
        else s!"[{lo}..{hi}]"
      | _, hi :: _ => s!"..{hi}"
      | lo :: _, _ => s!"{lo}.."
      | _, _ => "token"

/-- Annotated body CFG: src_addr → [(dataGuard, tgt_addr, returnAddr?)] -/
abbrev AnnotatedCFG := Std.HashMap UInt64 (Array (SymPC Amd64Reg × UInt64 × Option UInt64))

/-- Build annotated body CFG from raw body branches. -/
def buildAnnotatedBodyCFG (ip_reg : Amd64Reg)
    (bodyArr : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg))) :
    AnnotatedCFG × Std.HashSet UInt64 := Id.run do
  let mut cfg : AnnotatedCFG := {}
  let mut blocks : Std.HashSet UInt64 := {}
  for b in bodyArr do
    match extractRipGuard ip_reg b.pc, extractRipTarget ip_reg b.sub with
    | some src, some tgt =>
      blocks := blocks.insert src
      let guard := stripRipGuards ip_reg b.pc
      let ret := extractCallReturn b.sub.mem
      let edges := cfg.getD src #[]
      cfg := cfg.insert src (edges.push (guard, tgt, ret))
    | _, _ => pure ()
  return (cfg, blocks)

/-- DFS through body CFG collecting ordered call sequences as productions.
    Each external call (to next_sym or another NT) becomes one production symbol.
    The return address in memory is used to find the continuation after each call. -/
def dfsExtractProds
    (cur : UInt64)
    (steps : Array String)
    (cfg : AnnotatedCFG)
    (blocks : Std.HashSet UInt64)
    (funcEntries : Std.HashMap UInt64 String)
    (visited : Std.HashSet UInt64)
    (fuel : Nat := 61) :
    Array (Array String) :=
  match fuel with
  | 0 => #[steps]
  | fuel' + 1 => if visited.contains cur then #[steps] else Id.run do
  let visited' := visited.insert cur
  let edges := cfg.getD cur #[]
  if edges.isEmpty then
    return if steps.isEmpty then #[] else #[steps]
  let mut allPaths : Array (Array String) := #[]
  for (guard, tgt, retOpt) in edges do
    match funcEntries.get? tgt with
    | some "_exit" =>
      -- Error/abort path: drop this alternative (do not record, do not continue)
      pure ()
    | some callee =>
      -- External call: record as a production symbol
      let sym := if callee == "next_sym"
                 then describeCallSiteToken guard
                 else callee
      let steps' := steps.push sym
      match retOpt with
      | some ret =>
        if blocks.contains ret then
          allPaths := allPaths.append
            (dfsExtractProds ret steps' cfg blocks funcEntries visited' fuel')
        else
          allPaths := allPaths.push steps'  -- call is at function tail
      | none =>
        allPaths := allPaths.push steps'  -- can't determine continuation
    | none =>
      -- Internal transition, known-unknown helper, or function exit
      if blocks.contains tgt then
        -- Internal transition within this function: recurse without recording a step
        allPaths := allPaths.append
          (dfsExtractProds tgt steps cfg blocks funcEntries visited' fuel')
      else
        -- External call to unknown helper (e.g. a helper like isdigit called before next_sym).
        -- Follow the return address to find the continuation (the helper is transparent).
        match retOpt with
        | some ret =>
          if blocks.contains ret then
            allPaths := allPaths.append
              (dfsExtractProds ret steps cfg blocks funcEntries visited' fuel')
          else if !steps.isEmpty then
            allPaths := allPaths.push steps  -- tail call to unknown, end path
        | none =>
          if !steps.isEmpty then
            allPaths := allPaths.push steps  -- true exit
  return allPaths

/-- Golden grammar productions (from golden_grammar_tinyc.json).
    Each entry: (NT name, list of RHS alternatives as symbol sequences). -/
def goldenProds : Std.HashMap String (List (List String)) :=
  ({} : Std.HashMap String (List (List String)))
    |>.insert "term"       [["id"], ["int"], ["paren_expr"]]
    |>.insert "sum"        [["term"], ["sum", "'+'", "term"], ["sum", "'-'", "term"]]
    |>.insert "test"       [["sum"], ["sum", "'<'", "sum"]]
    |>.insert "expr"       [["test"], ["id", "'='", "expr"]]
    |>.insert "paren_expr" [["'('", "expr", "')'"]]
    |>.insert "statement"  [
        ["'if'", "paren_expr", "statement"],
        ["'if'", "paren_expr", "statement", "'else'", "statement"],
        ["'while'", "paren_expr", "statement"],
        ["'do'", "statement", "'while'", "paren_expr", "';'"],
        ["'{'", "statements", "'}'"],
        ["expr", "';'"],
        ["';'"]
      ]
    |>.insert "statements" [["statement"], ["statement", "statements"]]

/-- Strip angle brackets from golden grammar NT names: "<expr>" → "expr". -/
private def stripAngleBrackets (s : String) : String :=
  if s.startsWith "<" && s.endsWith ">" then
    (s.drop 1 |>.dropEnd 1).toString
  else s

/-- Load golden grammar from a stalagmite-format JSON file.
    Format: {"<nt>": [["sym1", "sym2"], ...], ...}
    Strips angle brackets from NT names and terminal symbols. -/
def loadGoldenGrammar (path : System.FilePath) : IO (Std.HashMap String (List (List String))) := do
  let contents ← IO.FS.readFile path
  match Lean.Json.parse contents with
  | .error e => IO.eprintln s!"Golden grammar parse error: {e}"; return {}
  | .ok json =>
    match json with
    | .obj kvs =>
      let mut result : Std.HashMap String (List (List String)) := {}
      for (key, val) in kvs.toArray do
        let ntName := stripAngleBrackets key
        match val with
        | .arr prods =>
          let mut prodList : List (List String) := []
          for prod in prods.reverse do
            match prod with
            | .arr syms =>
              let symList := syms.toList.filterMap fun s => match s with
                | .str sym => some (stripAngleBrackets sym)
                | _ => none
              prodList := symList :: prodList
            | _ => pure ()
          result := result.insert ntName prodList
        | _ => pure ()
      return result
    | _ => IO.eprintln s!"Golden grammar: expected JSON object"; return {}

/-- Try to load golden grammar for a subject from the stalagmite data directory.
    Looks for reference/../../../stalagmite/data/golden_grammars/golden_grammar_<subject>.json
    relative to the input file, or an absolute fallback path. -/
def loadGoldenForSubject (inputPath : System.FilePath) (log : String → IO Unit) :
    IO (Std.HashMap String (List (List String))) := do
  -- Extract subject name from path: reference/<subject>/blocks.json
  let components := inputPath.toString.splitOn "/"
  let subjectIdx := components.findIdx? (· == "reference")
  match subjectIdx with
  | some idx =>
    if idx + 1 < components.length then
      let subject := components[idx + 1]!
      -- Try stalagmite path relative to project root
      let projectRoot := "/".intercalate (components.take idx)
      let goldenPath := s!"{projectRoot}/../stalagmite/data/golden_grammars/golden_grammar_{subject}.json"
      if ← System.FilePath.pathExists goldenPath then
        log s!"  Loading golden grammar from {goldenPath}"
        loadGoldenGrammar goldenPath
      else
        -- Try absolute fallback
        let fallback := s!"/home/heartpunk/code/stalagmite/data/golden_grammars/golden_grammar_{subject}.json"
        if ← System.FilePath.pathExists fallback then
          log s!"  Loading golden grammar from {fallback}"
          loadGoldenGrammar fallback
        else
          log s!"  No golden grammar found for {subject}"
          return goldenProds  -- fall back to hardcoded tinyc
    else return goldenProds
  | none => return goldenProds

/-- BFS to find all blocks reachable from entry, following:
    - internal transitions (tgt in blocks)
    - return continuations after external calls (retOpt if tgt not in blocks) -/
def cfgReachable (entry : UInt64) (cfg : AnnotatedCFG) (blocks : Std.HashSet UInt64)
    (_funcEntries : Std.HashMap UInt64 String) :
    Std.HashSet UInt64 := Id.run do
  let mut visited : Std.HashSet UInt64 := {}
  let mut queue : Array UInt64 := #[entry]
  while !queue.isEmpty do
    let cur := queue.back!
    queue := queue.pop
    if visited.contains cur then pure ()
    else
      visited := visited.insert cur
      for (_, tgt, retOpt) in cfg.getD cur #[] do
        if blocks.contains tgt && !visited.contains tgt then
          queue := queue.push tgt   -- internal transition
        else
          -- external call: follow return continuation
          match retOpt with
          | some ret =>
            if blocks.contains ret && !visited.contains ret then
              queue := queue.push ret
          | none => pure ()
  return visited

/-- Extract productions for one NT function and print them with golden comparison. -/
def printFunctionProductions (log : String → IO Unit)
    (funcName : String) (entryAddr : UInt64)
    (bodyArr : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)))
    (funcEntries : Std.HashMap UInt64 String) : IO Unit := do
  let ip_reg := Amd64Reg.rip
  let (cfg, blocks) := buildAnnotatedBodyCFG ip_reg bodyArr
  let rawPaths := dfsExtractProds entryAddr #[] cfg blocks funcEntries {}
  -- Also explore orphan loop-body blocks (not reachable from entry via internal CFG).
  -- For NT calls (not next_sym) in orphan blocks, start DFS from the return continuation
  -- with the callee as the first step. This captures iterative loop alternatives like
  -- sum's "term '+' term" without spurious fragments from next_sym return sites.
  let reachable := cfgReachable entryAddr cfg blocks funcEntries
  let mut orphanPaths : Array (Array String) := #[]
  for (src, edges) in cfg.toArray do
    if reachable.contains src then pure ()  -- skip reachable blocks
    else
      for (_guard, tgt, retOpt) in edges do
        match funcEntries.get? tgt with
        | some "_exit" | some "next_sym" => pure ()  -- skip exit and terminals
        | some callee =>
          match retOpt with
          | some ret =>
            if blocks.contains ret then
              -- Start DFS from NT call's return continuation, with callee as first step
              orphanPaths := orphanPaths.append
                (dfsExtractProds ret #[callee] cfg blocks funcEntries {})
          | none => pure ()
        | none => pure ()
  -- Deduplicate
  let mut seen : Std.HashSet String := {}
  let mut unique : Array (Array String) := #[]
  for p in rawPaths.append orphanPaths do
    let key := " ".intercalate p.toList
    if !seen.contains key then
      seen := seen.insert key
      unique := unique.push p
  let golden := goldenProds.getD funcName []
  log s!"\n{funcName}: {unique.size} extracted productions (golden has {golden.length} alternatives)"
  for prod in unique do
    let rhs := if prod.isEmpty then "ε" else " ".intercalate prod.toList
    log s!"  {funcName} -> {rhs}"
  if !golden.isEmpty then
    log s!"  -- Golden:"
    for g in golden do
      log s!"  -- {funcName} -> {" ".intercalate g}"

/-- Print productions for all NT functions. -/
def printGrammarProductions (log : String → IO Unit)
    (functions : Array FunctionSpec)
    (funcEntries : Std.HashMap UInt64 String) : IO Unit := do
  log "\n=== Grammar Productions (Body CFG DFS) ==="
  let ip_reg := Amd64Reg.rip
  for i in [1:functions.size] do
    let func := functions[i]!
    match parseBlocksWithAddresses func.blocks with
    | .error e => log s!"  Parse error for {func.name}: {e}"
    | .ok pairs =>
      let bodyArr := flatBodyDenotArray ip_reg pairs
      printFunctionProductions log func.name func.entryAddr bodyArr funcEntries

/-- Extract CFG info from body branches: count next_sym calls and collect called NT names. -/
def extractBodyCFG (ip_reg : Amd64Reg)
    (bodyArr : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)))
    (funcEntries : Std.HashMap UInt64 String) : Nat × Std.HashSet String := Id.run do
  let mut nsCount : Nat := 0
  let mut calledNTs : Std.HashSet String := {}
  for b in bodyArr do
    match extractRipTarget ip_reg b.sub with
    | some tgt =>
      match funcEntries.get? tgt with
      | some name =>
        if name == "next_sym" then nsCount := nsCount + 1
        else calledNTs := calledNTs.insert name
      | none => pure ()
    | none => pure ()
  return (nsCount, calledNTs)

/-! ## Golden Grammar Comparison -/

/-- Expected callee NTs for each NT function (from golden_grammar_tinyc.json). -/
def goldenCallees : Std.HashMap String (List String) :=
  ({} : Std.HashMap String (List String))
    |>.insert "term"       ["paren_expr"]
    |>.insert "sum"        ["term"]  -- iterative impl: loop body, no recursive call
    |>.insert "test"       ["sum"]
    |>.insert "expr"       ["test", "expr"]
    |>.insert "paren_expr" ["expr"]
    |>.insert "statement"  ["paren_expr", "statement", "expr"]

/-- Expected: does each NT call next_sym (consume tokens)? -/
def goldenCallsNextSym : Std.HashMap String Bool :=
  ({} : Std.HashMap String Bool)
    |>.insert "term"       true   -- reads id or int tokens
    |>.insert "sum"        true   -- reads + or - token
    |>.insert "test"       true   -- reads < token
    |>.insert "expr"       true   -- reads = token (assignment alt)
    |>.insert "paren_expr" true   -- reads ( and ) tokens
    |>.insert "statement"  true   -- reads if/while/do/;/{/} tokens

/-- Compare extracted CFG with golden grammar and print results. -/
def printGrammarComparison (log : String → IO Unit)
    (extractedCFG : Std.HashMap String (Nat × List String)) : IO Unit := do
  log "\n=== Grammar Comparison (Extracted vs Golden) ==="
  let ntNames := ["term", "sum", "test", "expr", "paren_expr", "statement"]
  for name in ntNames do
    let (nsCount, calledNTs) := extractedCFG.getD name (0, [])
    let expectedCallees := goldenCallees.getD name []
    let expectedNS := goldenCallsNextSym.getD name false
    let callsNS := nsCount != 0
    -- Check if extracted callees contain all expected ones
    let calledSet : Std.HashSet String := calledNTs.foldl (fun s x => s.insert x) {}
    let missing := expectedCallees.filter (fun e => !calledSet.contains e)
    let ntOk := missing.isEmpty
    let nsOk := callsNS == expectedNS
    let status := if ntOk && nsOk then "OK" else "MISMATCH"
    let calledStr := ", ".intercalate calledNTs
    let expStr := ", ".intercalate expectedCallees
    let missingStr := if missing.isEmpty then "" else " MISSING=[" ++ ", ".intercalate missing ++ "]"
    log s!"  [{status}] {name}: next_sym={callsNS}(exp={expectedNS}) calls=[{calledStr}] exp=[{expStr}]{missingStr}"

/-! ## LTS Extraction from Converged Branches

The converged branch set IS the LTS implicitly — each branch encodes one
transition: src = rip guard address, tgt = rip target, label = decoded data
guard as a CharClass. Making it explicit enables DFA/EBNF specialization. -/

/-- A character/token class decoded from a data guard PC — regex style. -/
inductive CharClass where
  | literal : Char → CharClass          -- exact printable character match
  | tokenCode : UInt64 → CharClass      -- token type code (non-printable constant)
  | range : Char → Char → CharClass     -- inclusive character range [lo..hi]
  | negated : CharClass → CharClass     -- complement
  | conj : CharClass → CharClass → CharClass  -- intersection
  | any : CharClass                     -- any byte / epsilon
  | empty : CharClass                   -- contradictory / impossible guard
  deriving BEq, Hashable, Inhabited

/-- Render a CharClass as a regex-style string. -/
def CharClass.toString : CharClass → String
  | .literal c => s!"'{c}'"
  | .tokenCode n => s!"tok{n.toNat}"
  | .range lo hi => s!"[{lo}-{hi}]"
  | .negated (.literal c) => s!"[^{c}]"
  | .negated cc => s!"[^{cc.toString}]"
  | .conj a b => s!"{a.toString}&{b.toString}"
  | .any => "."
  | .empty => "∅"

instance : ToString CharClass := ⟨CharClass.toString⟩

/-- Extract a small constant from a wrapped SymExpr (strips sext, zext, low32, add64).
    Unlike stripToCharConst, accepts ALL constants < 256, not just printable. -/
def stripToSmallConst : SymExpr Amd64Reg → Option UInt64
  | .const v => if v.toNat < 256 then some v else none
  | .low32 inner | .uext32 inner | .sext8to32 inner | .sext32to64 inner =>
    stripToSmallConst inner
  | .add64 a b => stripToSmallConst a <|> stripToSmallConst b
  | _ => none

/-- Check if a SymExpr loads via register-relative addresses, indicating a local
    variable rather than the global `sym` variable. The global `sym` is accessed
    through a chain of loads from constant addresses (e.g., load(mem, load(mem, 0x500030))).
    Local variables use register-relative addresses (e.g., load(mem, rbp-16)). -/
def exprLoadsViaRegAddr : SymExpr Amd64Reg → Bool
  | .load _ _ addr => addrUsesRegs addr
  | .low32 e | .uext32 e | .sext8to32 e | .sext32to64 e | .not64 e | .not32 e => exprLoadsViaRegAddr e
  | .ite c t f => exprLoadsViaRegAddr c || exprLoadsViaRegAddr t || exprLoadsViaRegAddr f
  | .add64 a b | .sub64 a b | .xor64 a b | .and64 a b | .or64 a b
  | .sub32 a b | .shl32 a b | .and32 a b | .or32 a b | .xor32 a b | .shl64 a b | .shr64 a b | .mul64 a b | .mul32 a b | .sar64 a b | .sar32 a b => exprLoadsViaRegAddr a || exprLoadsViaRegAddr b
  | _ => false
where
  /-- Check if an address expression uses registers (for load address chains). -/
  addrUsesRegs : SymExpr Amd64Reg → Bool
  | .reg _ => true
  | .const _ => false
  | .load _ _ innerAddr => addrUsesRegs innerAddr  -- chained load: check inner address
  | .add64 a b | .sub64 a b | .xor64 a b | .and64 a b | .or64 a b
  | .sub32 a b | .shl32 a b | .and32 a b | .or32 a b | .xor32 a b | .shl64 a b | .shr64 a b | .mul64 a b | .mul32 a b | .sar64 a b | .sar32 a b => addrUsesRegs a || addrUsesRegs b
  | .low32 e | .uext32 e | .sext8to32 e | .sext32to64 e | .not64 e | .not32 e => addrUsesRegs e
  | .ite c t f => addrUsesRegs c || addrUsesRegs t || addrUsesRegs f

/-- Extract a constant (printable char or token code) from a SymExpr. -/
def extractConstFromExpr (e : SymExpr Amd64Reg) : Option (CharClass) :=
  match stripToSmallConst e with
  | some v =>
    let n := v.toNat
    if n ≥ 32 && n ≤ 126 then some (.literal (Char.ofNat n))
    else some (.tokenCode v)
  | none => none

/-- Decode a single SymPC atom into a CharClass component.
    Uses extractConstFromExpr to handle VEX-style wrapped expressions
    and both printable characters AND non-printable token type codes. -/
private def decodeAtom (pc : SymPC Amd64Reg) : Option CharClass :=
  match pc with
  | .eq l r =>
    -- Extract constants from both sides, but skip when the other side loads via
    -- register-relative address, indicating a local variable comparison, not a sym check.
    let cl := if exprLoadsViaRegAddr r then none else extractConstFromExpr l
    let cr := if exprLoadsViaRegAddr l then none else extractConstFromExpr r
    match cl <|> cr with
    | some cc => some cc
    | none => none
  | .le l r =>
    -- For range bounds, we still need character values
    let lChar := extractCharConstFromExpr l
    let rChar := extractCharConstFromExpr r
    match lChar, rChar with
    | some lo, none => some (.range lo (Char.ofNat 127))
    | none, some hi => some (.range (Char.ofNat 0) hi)
    | _, _ => none
  | .lt l r =>
    let lChar := extractCharConstFromExpr l
    let rChar := extractCharConstFromExpr r
    match lChar, rChar with
    | some lo, none =>
      some (.range (Char.ofNat (lo.toNat + 1)) (Char.ofNat 127))
    | none, some hi =>
      if hi.toNat > 0 then some (.range (Char.ofNat 0) (Char.ofNat (hi.toNat - 1)))
      else none
    | _, _ => none
  | .not inner =>
    match decodeAtom inner with
    | some cc => some (.negated cc)
    | none => none
  | _ => none

/-- Decode a full data guard PC into a CharClass.
    Collects decoded atoms, intersects ranges to produce compact classes. -/
def decodeCharClass (pc : SymPC Amd64Reg) : CharClass :=
  let atoms := SymPC.conjuncts pc
  let decoded := atoms.filterMap decodeAtom
  match decoded with
  | [] => .any
  | [c] => c
  | c :: rest => rest.foldl .conj c

/-- Simplify a pair of CharClass values under conjunction.
    Returns none if the pair doesn't match any special rule. -/
private def CharClass.simplifyPair (a b : CharClass) : Option CharClass :=
  match a, b with
  -- empty propagation
  | .empty, _ | _, .empty => some .empty
  -- any is identity for conj
  | .any, x | x, .any => some x
  -- range ∩ range → narrower range
  | .range lo1 hi1, .range lo2 hi2 =>
    let lo := if lo1 > lo2 then lo1 else lo2
    let hi := if hi1 < hi2 then hi1 else hi2
    if lo == hi then some (.literal lo)
    else if lo < hi then some (.range lo hi)
    else some .empty
  -- literal ∩ range
  | .literal c, .range lo hi | .range lo hi, .literal c =>
    if c >= lo && c <= hi then some (.literal c) else some .empty
  -- tokenCode ∩ tokenCode
  | .tokenCode a, .tokenCode b =>
    if a == b then some (.tokenCode a) else some .empty
  -- tokenCode ∩ negated(tokenCode)
  | .tokenCode a, .negated (.tokenCode b) | .negated (.tokenCode b), .tokenCode a =>
    if a == b then some .empty else some (.tokenCode a)
  -- literal ∩ negated(literal)
  | .literal a, .negated (.literal b) | .negated (.literal b), .literal a =>
    if a == b then some .empty else some (.literal a)
  -- literal ∩ literal
  | .literal a, .literal b =>
    if a == b then some (.literal a) else some .empty
  | _, _ => none

/-- Flatten a conjunction tree into a list of conjuncts. -/
def CharClass.flattenConj : CharClass → List CharClass
  | .conj a b => a.flattenConj ++ b.flattenConj
  | other => [other]

/-- Simplify a flat list of conjuncts: if there is exactly one positive tokenCode
    and all other conjuncts are negated tokenCodes with different values, simplify
    to just the positive tokenCode. Also handles positive literal + negated tokenCodes. -/
def CharClass.simplifyFlat (parts : List CharClass) : Option CharClass :=
  let positives := parts.filter fun
    | .tokenCode _ | .literal _ | .range _ _ => true
    | _ => false
  let negatives := parts.filter fun
    | .negated _ => true
    | _ => false
  -- If exactly one positive and the rest are negatives, check consistency
  if positives.length == 1 && positives.length + negatives.length == parts.length then
    let pos := positives.head!
    let allConsistent := negatives.all fun
      | .negated (.tokenCode b) =>
        match pos with
        | .tokenCode a => a != b  -- negating a different code is consistent
        | .literal _ | .range _ _ => true  -- negating tokenCode is consistent with literal/range
        | _ => false
      | .negated (.literal b) =>
        match pos with
        | .literal a => a != b
        | .tokenCode _ | .range _ _ => true
        | _ => false
      | _ => false
    if allConsistent then some pos else none
  else none

/-- Simplify a CharClass by intersecting ranges and resolving conjunctions. -/
def CharClass.simplify : CharClass → CharClass
  | .conj a b =>
    let a' := a.simplify
    let b' := b.simplify
    match CharClass.simplifyPair a' b' with
    | some result => result
    | none =>
      -- Try flatten-and-simplify for multi-level conjunctions
      let flat := CharClass.flattenConj (.conj a' b')
      match CharClass.simplifyFlat flat with
      | some result => result
      | none => .conj a' b'
  | .negated inner => match inner.simplify with
    | .empty => .any  -- negation of empty = everything (but shouldn't arise)
    | inner' => .negated inner'
  | other => other

/-- Token name table: maps token type codes to human-readable names.
    Built from converged next_sym summary (rax at return → token name). -/
abbrev TokenNameTable := Std.HashMap UInt64 String

/-- Infer a token class name from a CharClass, using optional token name table. -/
def charClassToTokenName (tokenNames : TokenNameTable := {}) : CharClass → String
  | .literal c => s!"'{c}'"
  | .tokenCode n =>
    match tokenNames.get? n with
    | some name => name
    | none => s!"tok{n.toNat}"
  | .range lo hi => s!"[{lo}-{hi}]"
  | .negated cc => s!"[^{cc}]"
  | .any => "token"
  | .empty => "∅"
  | cc => cc.toString

/-- A single LTS transition: source state, label, target state. -/
structure LTSTransition where
  src : UInt64
  label : CharClass
  tgt : UInt64
  deriving BEq, Hashable

/-- An extracted LTS: states are block addresses, labels are CharClasses. -/
structure ExtractedLTS where
  transitions : Array LTSTransition
  states : Std.HashSet UInt64
  deriving Inhabited

/-- Find the largest block entry address that is ≤ the given address.
    Redirects mid-block jump targets to the containing block's entry. -/
def redirectToBlockEntry (addr : UInt64) (sortedEntries : Array UInt64) : UInt64 := Id.run do
  let mut best := addr
  for entry in sortedEntries do
    if entry <= addr then best := entry
  return best

/-- Extract an LTS from an array of converged branches.
    Each branch yields: src = rip guard, tgt = rip target, label = data guard decoded.
    Mid-block jump targets are redirected to the containing block's entry address. -/
def extractLTS (ip_reg : Amd64Reg)
    (branches : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)))
    (funcEntries : Std.HashMap UInt64 String := {}) :
    ExtractedLTS :=
  -- First pass: collect block entry addresses (sources)
  let blockEntries := Id.run do
    let mut entries : Std.HashSet UInt64 := {}
    for b in branches do
      match extractRipGuard ip_reg b.pc with
      | some src => entries := entries.insert src
      | none => pure ()
    return entries.toArray.qsort (· < ·)
  let blockSet : Std.HashSet UInt64 := blockEntries.foldl (fun s e => s.insert e) {}
  -- Second pass: extract transitions, redirecting mid-block targets
  let trans := Id.run do
    let mut trans : Array LTSTransition := #[]
    for b in branches do
      match extractRipGuard ip_reg b.pc, extractRipTarget ip_reg b.sub with
      | some src, some tgt =>
        let dataGuard := stripRipGuards ip_reg b.pc
        let label := (decodeCharClass dataGuard).simplify
        -- Redirect mid-block targets to containing block entry
        let tgt' := if blockSet.contains tgt || funcEntries.contains tgt then tgt
                    else redirectToBlockEntry tgt blockEntries
        trans := trans.push ⟨src, label, tgt'⟩
      | _, _ => pure ()
    return trans
  let states := trans.foldl (fun s t => (s.insert t.src).insert t.tgt) ({} : Std.HashSet UInt64)
  { transitions := trans, states := states }

/-- Print an LTS transition table. -/
def printLTS (log : String → IO Unit) (name : String) (lts : ExtractedLTS) : IO Unit := do
  log s!"\n=== LTS: {name} ({lts.transitions.size} transitions, {lts.states.size} states) ==="
  -- Group by source
  let mut bySource : Std.HashMap UInt64 (Array LTSTransition) := {}
  for t in lts.transitions do
    let arr := bySource.getD t.src #[]
    bySource := bySource.insert t.src (arr.push t)
  for (src, edges) in bySource.toArray do
    log s!"  {hexAddr src}:"
    for t in edges do
      log s!"    --[{t.label}]--> {hexAddr t.tgt}"

/-! ## DFA Specialization for Tokenizer -/

/-- A DFA state: block address, whether it's accepting, and if so the token type. -/
structure DFAState where
  addr : UInt64
  isAccept : Bool
  tokenType : Option String  -- rax value at return → token class
  deriving Inhabited

/-- Extract the rax value from a branch's substitution for token type identification. -/
def extractRaxValue (sub : SymSub Amd64Reg) : Option String :=
  match sub.regs .rax with
  | .const v =>
    let n := v.toNat
    if n ≥ 32 && n ≤ 126 then some s!"'{Char.ofNat n}'"
    else some s!"{n}"
  | _ => none

/-- Print DFA for next_sym: transitions, accept states with token types. -/
def printTokenizerDFA (log : String → IO Unit)
    (lts : ExtractedLTS)
    (funcBlocks : Std.HashSet UInt64)
    (bodyBranches : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)))
    (entryAddr : UInt64) : IO Unit := do
  log s!"\n=== Tokenizer DFA (next_sym) ==="
  log s!"  entry: {hexAddr entryAddr}"
  -- Accept states: transitions whose target is outside the function's block set
  let mut acceptTokens : Std.HashMap UInt64 String := {}  -- src → token type
  for b in bodyBranches do
    match extractRipGuard Amd64Reg.rip b.pc, extractRipTarget Amd64Reg.rip b.sub with
    | some src, some tgt =>
      if !funcBlocks.contains tgt then
        -- This is a return transition; extract rax as token type
        let tok := match extractRaxValue b.sub with
          | some v => v
          | none => "?"
        acceptTokens := acceptTokens.insert src tok
    | _, _ => pure ()
  log s!"  accept states: {acceptTokens.size}"
  for (addr, tok) in acceptTokens.toArray do
    log s!"    {hexAddr addr} → token={tok}"
  -- Print transitions (only internal ones within next_sym)
  let mut bySource : Std.HashMap UInt64 (Array LTSTransition) := {}
  let mut internalCount := 0
  for t in lts.transitions do
    if funcBlocks.contains t.src && funcBlocks.contains t.tgt then
      let arr := bySource.getD t.src #[]
      bySource := bySource.insert t.src (arr.push t)
      internalCount := internalCount + 1
  log s!"  internal transitions: {internalCount}"
  for (src, edges) in bySource.toArray do
    let acceptMark := if acceptTokens.contains src then s!" [accept→{acceptTokens.get! src}]" else ""
    log s!"  {hexAddr src}{acceptMark}:"
    for t in edges do
      log s!"    --[{t.label}]--> {hexAddr t.tgt}"

/-! ## Parser Detection — Conservative Constructive Evidence

Given converged function summaries from stratified fixpoint, detect whether
the binary is a parser and construct a ParserStructure with:
- Which function is the lexer (token producer)
- Which functions are nonterminals (token consumers)
- Derived token names from lexer branch guards

Detection uses IsTokenConfig (World 1, rax proxy): the lexer is the unique
function that produces diverse rax constants, called by ≥2 consumer functions. -/

/-- How the binary classifies an LTS transition. -/
inductive TransitionRole where
  | terminal : TransitionRole              -- consumes a token
  | nonterminal : String → TransitionRole  -- invokes another classifier
  | internal : TransitionRole              -- function-internal (not grammar-relevant)

/-- Evidence that a binary classifies regions of a token stream.
    Construction-method-agnostic: IsTokenConfig, World 2 detection, or
    manual annotation all produce the same structure. -/
structure ParserStructure where
  /-- The region classifiers (nonterminals) -/
  classifiers : Array FunctionSpec
  /-- The lexer function name -/
  lexerName : String
  /-- The lexer function entry address -/
  lexerAddr : UInt64
  /-- Which classifier is the entry point (start symbol) -/
  entryClassifier : UInt64
  /-- Token name table for rendering -/
  tokenNames : TokenNameTable

/-- Evidence for IsTokenConfig conditions (Bool witnesses). -/
structure TokenConfigEvidence where
  lexer : FunctionSpec
  raxValues : Array UInt64
  consumers : Array FunctionSpec
  callEdges : Array (UInt64 × UInt64)
  deriving Inhabited

/-- Extract the raw rax UInt64 from a branch substitution (for producer detection). -/
def extractRaxValueRaw (sub : SymSub Amd64Reg) : Option UInt64 :=
  match sub.regs .rax with
  | .const v => some v
  | _ => none

/-- Resolve a SymExpr to a constant, substituting known rip value.
    Handles patterns like add64(reg(rip), const(offset)), const(v), etc. -/
def resolveExprConst (ripVal : Option UInt64) : SymExpr Amd64Reg → Option UInt64
  | .const v => some v
  | .reg .rip => ripVal
  | .add64 a b => do
    let va ← resolveExprConst ripVal a
    let vb ← resolveExprConst ripVal b
    return va + vb
  | .sub64 a b => do
    let va ← resolveExprConst ripVal a
    let vb ← resolveExprConst ripVal b
    return va - vb
  | .low32 inner => do
    let v ← resolveExprConst ripVal inner
    return v &&& 0xFFFFFFFF
  | .sext32to64 inner => resolveExprConst ripVal inner
  | .uext32 inner => resolveExprConst ripVal inner
  | _ => none

/-- Extract (address, value) pairs from constant stores in a memory chain.
    Resolves RIP-relative addresses using the known rip value from the branch's PC guard.
    Returns array of (store_addr, stored_value). -/
def extractConstStores (ripVal : Option UInt64) : SymMem Amd64Reg → Array (UInt64 × UInt64)
  | .base => #[]
  | .store _w inner addr val =>
    let rest := extractConstStores ripVal inner
    match resolveExprConst ripVal addr, resolveExprConst ripVal val with
    | some a, some v => rest.push (a, v)
    | _, _ => rest

/-- Build call graph by scanning raw body branches for rip targets matching function entries.
    Returns array of (caller_addr, callee_addr) edges. -/
def buildCallGraph
    (functions : Array FunctionSpec)
    (log : String → IO Unit) :
    IO (Array (UInt64 × UInt64)) := do
  let ip_reg := Amd64Reg.rip
  let mut funcEntrySet : Std.HashSet UInt64 := {}
  for f in functions do
    funcEntrySet := funcEntrySet.insert f.entryAddr
  let mut edges : Array (UInt64 × UInt64) := #[]
  for func in functions do
    match parseBlocksWithAddresses func.blocks with
    | .error _ => pure ()
    | .ok pairs =>
      let bodyArr := flatBodyDenotArray ip_reg pairs
      for b in bodyArr do
        match extractRipTarget ip_reg b.sub with
        | some tgt =>
          if funcEntrySet.contains tgt && tgt != func.entryAddr then
            let edgeExists := edges.any fun (s, t) => s == func.entryAddr && t == tgt
            if !edgeExists then
              edges := edges.push (func.entryAddr, tgt)
        | none => pure ()
  log s!"\n=== Parser Detection: Call Graph ({edges.size} edges) ==="
  for (src, tgt) in edges do
    let srcName := functions.findSome? fun f => if f.entryAddr == src then some f.name else none
    let tgtName := functions.findSome? fun f => if f.entryAddr == tgt then some f.name else none
    log s!"  {srcName.getD (hexAddr src)} → {tgtName.getD (hexAddr tgt)}"
  return edges

/-- Find producer functions: those that write ≥2 distinct constant values to the SAME
    memory address on return transitions. This detects the token variable (e.g., `sym`)
    without requiring rax to carry the return value.
    Returns array of (function addr, distinct token values, token variable address). -/
def findProducers
    (functions : Array FunctionSpec)
    (_summaries : Std.HashMap UInt64 (Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg))))
    (log : String → IO Unit) :
    IO (Array (UInt64 × Array UInt64)) := do
  let ip_reg := Amd64Reg.rip
  let mut producers : Array (UInt64 × Array UInt64) := #[]
  log s!"\n--- Producer Identification ---"
  for func in functions do
    match parseBlocksWithAddresses func.blocks with
    | .error _ =>
      log s!"  {func.name}: PARSE ERROR"
    | .ok pairs =>
      let bodyArr := flatBodyDenotArray ip_reg pairs
      -- Build block set to identify return transitions
      let mut funcBlocks : Std.HashSet UInt64 := {}
      for b in bodyArr do
        match extractRipGuard ip_reg b.pc with
        | some src => funcBlocks := funcBlocks.insert src
        | none => pure ()
      -- Scan ALL body branches for stores of constants to the same address expression.
      -- The token variable (e.g., sym) is accessed through GOT dereference:
      --   store(val, load(mem, GOT_addr)) — same address expr, different constant vals.
      -- Group by (address expression hash) → collect distinct constant values.
      let mut storesByExprHash : Std.HashMap UInt64 (SymExpr Amd64Reg × Std.HashSet UInt64) := {}
      for b in bodyArr do
        match b.sub.mem with
        | .base => pure ()
        | _ =>
          -- Walk store chain, collect (addr_expr, const_value) pairs
          let mut mem := b.sub.mem
          let mut done := false
          while !done do
            match mem with
            | .store _w inner addr val =>
              -- Skip stack stores (addr uses rsp/rbp)
              let isStack := exprUsesRSP addr
              match resolveExprConst none val with
              | some constVal =>
                if !isStack then
                  let h := hash addr
                  let (expr, vals) := storesByExprHash.getD h (addr, {})
                  storesByExprHash := storesByExprHash.insert h (expr, vals.insert constVal)
              | none => pure ()
              mem := inner
            | .base => done := true
      -- Find the address expression with the most distinct values
      let mut bestHash : UInt64 := 0
      let mut bestCount : Nat := 0
      let mut bestExpr : Option (SymExpr Amd64Reg) := none
      for (h, (expr, vals)) in storesByExprHash.toArray do
        if vals.size > bestCount then
          bestHash := h
          bestCount := vals.size
          bestExpr := some expr
      -- Also check rax across all branches
      let mut raxVals : Std.HashSet UInt64 := {}
      for b in bodyArr do
        match extractRaxValueRaw b.sub with
        | some v => raxVals := raxVals.insert v
        | none => pure ()
      let (tokenVals, source) :=
        if bestCount >= raxVals.size && bestCount >= 2 then
          let (_, vals) := storesByExprHash.getD bestHash (SymExpr.const 0, {})
          (vals.toArray, s!"mem[{bestExpr.map (exprSummary · 3) |>.getD "?"}]")
        else if raxVals.size >= 2 then
          (raxVals.toArray, "rax")
        else
          (#[], "none")
      log s!"  {func.name}: {bodyArr.size} body branches, best_mem={bestCount} vals @ {bestExpr.map (exprSummary · 3) |>.getD "none"}, rax={raxVals.size} distinct"
      if tokenVals.size >= 2 then
        producers := producers.push (func.entryAddr, tokenVals)
        log s!"    → Producer candidate via {source} ({tokenVals.size} distinct values)"
  return producers

/-- Find consumer functions: those that call the producer in the call graph. -/
def findConsumers
    (functions : Array FunctionSpec)
    (callGraph : Array (UInt64 × UInt64))
    (producerAddr : UInt64)
    (log : String → IO Unit) :
    IO (Array FunctionSpec) := do
  let mut consumers : Array FunctionSpec := #[]
  for func in functions do
    if func.entryAddr == producerAddr then continue
    let callsProducer := callGraph.any fun (src, tgt) =>
      src == func.entryAddr && tgt == producerAddr
    if callsProducer then
      consumers := consumers.push func
      log s!"  Consumer: {func.name} @ {hexAddr func.entryAddr}"
  return consumers

/-- Check IsTokenConfig conditions: unique producer with ≥2 consumers.
    Returns the token config evidence or an error explaining why detection failed. -/
def checkTokenConfig
    (functions : Array FunctionSpec)
    (producers : Array (UInt64 × Array UInt64))
    (callGraph : Array (UInt64 × UInt64))
    (log : String → IO Unit) :
    IO (Except String TokenConfigEvidence) := do
  log s!"\n--- IsTokenConfig Check ---"
  if producers.isEmpty then
    log "  FAIL: No producer candidates (no function with ≥2 distinct rax values)"
    return .error "No producer function found"
  let mut validConfigs : Array TokenConfigEvidence := #[]
  for (addr, raxVals) in producers do
    let func := functions.find? fun f => f.entryAddr == addr
    match func with
    | some f =>
      let consumers ← findConsumers functions callGraph addr log
      if consumers.size >= 2 then
        log s!"  Producer {f.name}: {consumers.size} consumers — VALID"
        validConfigs := validConfigs.push {
          lexer := f
          raxValues := raxVals
          consumers := consumers
          callEdges := callGraph
        }
      else
        log s!"  Producer {f.name}: only {consumers.size} consumers — REJECTED (need ≥2)"
    | none => pure ()
  match validConfigs.size with
  | 0 =>
    log "  FAIL: No producer with ≥2 consumers"
    return .error "No producer with ≥2 consumers"
  | 1 =>
    log s!"  PASS: Unique producer {validConfigs[0]!.lexer.name} with {validConfigs[0]!.consumers.size} consumers"
    return .ok validConfigs[0]!
  | n =>
    log s!"  FAIL: Ambiguous — {n} producers each with ≥2 consumers"
    return .error s!"Ambiguous: {n} valid producers"

/-- Find entry point: the NT function not called by any other NT.
    Falls back to first NT if all are mutually recursive. -/
def findParserEntryPoint
    (ntFunctions : Array FunctionSpec)
    (callGraph : Array (UInt64 × UInt64))
    (log : String → IO Unit) :
    IO UInt64 := do
  let candidates := ntFunctions.filter fun f =>
    !(callGraph.any fun (src, tgt) =>
      tgt == f.entryAddr && (ntFunctions.any fun g => g.entryAddr == src))
  match candidates[0]? with
  | some f =>
    log s!"  Entry point: {f.name} (not called by any other NT)"
    return f.entryAddr
  | none =>
    match ntFunctions[0]? with
    | some f =>
      log s!"  Entry point: {f.name} (fallback — all NTs mutually recursive)"
      return f.entryAddr
    | none => return 0

/-- Classify functions: identify NTs (not lexer, transitively calls lexer).
    Returns (NTs, helpers). -/
def classifyParserFunctions
    (functions : Array FunctionSpec)
    (callGraph : Array (UInt64 × UInt64))
    (lexerAddr : UInt64)
    (log : String → IO Unit) :
    IO (Array FunctionSpec × Array FunctionSpec) := do
  log s!"\n--- Function Classification ---"
  let mut adj : Std.HashMap UInt64 (Array UInt64) := {}
  for (src, tgt) in callGraph do
    let arr := adj.getD src #[]
    adj := adj.insert src (arr.push tgt)
  let callsLexer (startAddr : UInt64) : Bool := Id.run do
    let mut visited : Std.HashSet UInt64 := {}
    let mut queue : Array UInt64 := #[startAddr]
    while !queue.isEmpty do
      let cur := queue.back!
      queue := queue.pop
      if visited.contains cur then continue
      visited := visited.insert cur
      if cur == lexerAddr then return true
      for tgt in adj.getD cur #[] do
        if !visited.contains tgt then
          queue := queue.push tgt
    return false
  let mut nts : Array FunctionSpec := #[]
  let mut helpers : Array FunctionSpec := #[]
  for func in functions do
    if func.entryAddr == lexerAddr then
      log s!"  {func.name}: LEXER"
    else
      let transCallsLex := callsLexer func.entryAddr
      if transCallsLex then
        nts := nts.push func
        log s!"  {func.name}: NT (transitively calls lexer)"
      else
        helpers := helpers.push func
        log s!"  {func.name}: HELPER (does not call lexer)"
  return (nts, helpers)

/-- Derive token names from the lexer's raw body branches.
    For each summary branch that stores a constant to the token variable,
    decode the data guard as CharClass. Uses summary branches (post-fixpoint)
    because multi-block character comparisons are composed into single guards. -/
def deriveTokenNames
    (lexerSpec : FunctionSpec)
    (summaryBranches : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)))
    (log : String → IO Unit) :
    IO TokenNameTable := do
  let ip_reg := Amd64Reg.rip
  -- Use SUMMARY branches (post-fixpoint) for token name derivation.
  -- Summary branches have composed guards that include the full character class
  -- (multi-block paths are already collapsed).
  -- Step 1: Find the token variable address expression from summary branches.
  let mut storesByExprHash : Std.HashMap UInt64 (SymExpr Amd64Reg × Std.HashSet UInt64) := {}
  for b in summaryBranches do
    match b.sub.mem with
    | .base => pure ()
    | _ =>
      let mut mem := b.sub.mem
      let mut done := false
      while !done do
        match mem with
        | .store _w inner addr val =>
          let isStack := exprUsesRSP addr
          match resolveExprConst none val with
          | some constVal =>
            if !isStack then
              let h := hash addr
              let (expr, vals) := storesByExprHash.getD h (addr, {})
              storesByExprHash := storesByExprHash.insert h (expr, vals.insert constVal)
          | none => pure ()
          mem := inner
        | .base => done := true
  let mut bestHash : UInt64 := 0
  let mut bestCount : Nat := 0
  for (h, (_, vals)) in storesByExprHash.toArray do
    if vals.size > bestCount then
      bestHash := h
      bestCount := vals.size
  -- Step 2: For each summary branch that stores a constant to the token variable,
  -- extract the constant and decode the branch's data guard (character class).
  let mut table : TokenNameTable := {}
  if bestCount >= 2 then
    for b in summaryBranches do
      match b.sub.mem with
      | .base => pure ()
      | _ =>
        let mut mem := b.sub.mem
        let mut done := false
        while !done do
          match mem with
          | .store _w inner addr val =>
            let isStack := exprUsesRSP addr
            if !isStack && hash addr == bestHash then
              match resolveExprConst none val with
              | some constVal =>
                if !table.contains constVal then
                  let dataGuard := stripRipGuards ip_reg b.pc
                  let cc := (decodeCharClass dataGuard).simplify
                  -- Only add to table if we decoded a meaningful character class
                  -- (.any means we couldn't decode anything — no information)
                  match cc with
                  | .any => pure ()
                  | _ =>
                    let name := charClassToTokenName {} cc
                    table := table.insert constVal name
              | none => pure ()
            mem := inner
          | .base => done := true
  -- Fallback: try body-level rax extraction
  if table.size == 0 then
    match parseBlocksWithAddresses lexerSpec.blocks with
    | .error _ => pure ()
    | .ok pairs =>
      let bodyArr := flatBodyDenotArray ip_reg pairs
      let mut lexerBlocks : Std.HashSet UInt64 := {}
      for b in bodyArr do
        match extractRipGuard ip_reg b.pc with
        | some src => lexerBlocks := lexerBlocks.insert src
        | none => pure ()
      for b in bodyArr do
        match extractRaxValueRaw b.sub with
        | some raxVal =>
          if table.contains raxVal then continue
          match extractRipTarget ip_reg b.sub with
          | some tgt =>
            if !lexerBlocks.contains tgt then
              let dataGuard := stripRipGuards ip_reg b.pc
              let cc := (decodeCharClass dataGuard).simplify
              match cc with
              | .any => pure ()
              | _ =>
                let name := charClassToTokenName {} cc
                table := table.insert raxVal name
          | none => pure ()
        | none => pure ()
  log s!"\n--- Derived Token Names ({table.size} entries) ---"
  for (code, name) in table.toArray do
    log s!"  {code.toNat} → {name}"
  return table

/-- Detect parser structure from converged function summaries.
    Uses IsTokenConfig (World 1, rax proxy) to identify lexer and NTs. -/
def detectParser
    (functions : Array FunctionSpec)
    (summaries : Std.HashMap UInt64 (Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg))))
    (log : String → IO Unit) :
    IO (Except String ParserStructure) := do
  log "\n=== Parser Detection ==="
  let callGraph ← buildCallGraph functions log
  let producers ← findProducers functions summaries log
  match ← checkTokenConfig functions producers callGraph log with
  | .error e =>
    log s!"  Parser detection FAILED: {e}"
    return .error e
  | .ok evidence =>
    let (nts, _helpers) ← classifyParserFunctions functions callGraph evidence.lexer.entryAddr log
    let entryAddr ← findParserEntryPoint nts callGraph log
    let lexerSummary := summaries.getD evidence.lexer.entryAddr #[]
    let tokenNames ← deriveTokenNames evidence.lexer lexerSummary log
    let ps : ParserStructure := {
      classifiers := nts
      lexerName := evidence.lexer.name
      lexerAddr := evidence.lexer.entryAddr
      entryClassifier := entryAddr
      tokenNames := tokenNames
    }
    log s!"\n--- Parser Detection SUCCEEDED ---"
    log s!"  Lexer: {ps.lexerName} @ {hexAddr ps.lexerAddr}"
    log s!"  NTs: {nts.toList.map (·.name)}"
    log s!"  Entry: {hexAddr ps.entryClassifier}"
    log s!"  Token names: {ps.tokenNames.size} entries"
    return .ok ps

/-! ## EBNF Extraction from LTS

For each NT function, walk the LTS to produce EBNF productions:
- Transitions to lexer entry = terminal (token type from data guard label)
- Transitions to other NT entry = nonterminal reference
- Linear chains = sequence
- Branch points = alternatives
- Back edges = repetition

CRITICAL: alternatives are distinguished by BOTH target AND label.
This fixes term getting 2/3 — id and int both call next_sym but with
different character class labels (letters vs digits). -/

/-- An EBNF symbol: terminal token or nonterminal reference. -/
inductive GrammarSym where
  | terminal : CharClass → GrammarSym     -- raw guard, rendered via charClassToTokenName
  | nonterminal : String → GrammarSym     -- function name or synthetic loop NT
  deriving BEq, Hashable, Inhabited

def GrammarSym.isTerminal : GrammarSym → Bool
  | .terminal _ => true
  | .nonterminal _ => false

/-- Check if a CharClass is a single positive tokenCode. -/
def CharClass.isPositiveTokenCode : CharClass → Option UInt64
  | .tokenCode n => some n
  | _ => none

/-- DFS result: either completed productions, or a loop detected back to a target node. -/
inductive DFSResult where
  | productions : Array (Array GrammarSym) → DFSResult
  | loopDetected : UInt64 → Array GrammarSym → DFSResult  -- target, loop body

/-- DFS through LTS collecting ordered symbol sequences as grammar productions.
    Accumulates CharClass labels along internal transitions (accGuard) so that
    data guards from upstream comparison blocks classify tokens (e.g., id vs int).
    Loop recognition: back-edge detection via nodeStepIdx produces left-recursive
    productions: `funcName ++ steps[idx:]` (e.g., sum '+' term).
    Guard-based NT specialization: when calling an NT with accumulated guard that
    simplifies to a single positive tokenCode, emit terminal instead of nonterminal. -/
def ltsExtractProds
    (cur : UInt64)
    (steps : Array GrammarSym)
    (accGuard : CharClass)
    (ltsMap : Std.HashMap UInt64 (Array LTSTransition))
    (funcBlocks : Std.HashSet UInt64)
    (funcEntries : Std.HashMap UInt64 String)
    (visited : Std.HashSet UInt64)
    (nodeStepIdx : Std.HashMap UInt64 Nat)
    (funcName : String)
    (fuel : Nat)
    (bodyBranches : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)))
    (lexerName : String := "next_sym")
    (tokenNames : TokenNameTable := {}) :
    Array (Array GrammarSym) :=
  match fuel with
  | 0 => #[steps]
  | fuel' + 1 => Id.run do
  if visited.contains cur then
    -- Back-edge detected: create left-recursive production
    match nodeStepIdx.get? cur with
    | some idx =>
      let loopBody := steps.extract idx steps.size
      if loopBody.isEmpty then return #[steps]
      else return #[#[.nonterminal funcName] ++ loopBody]
    | none => return #[steps]
  let visited' := visited.insert cur
  let nodeStepIdx' := nodeStepIdx.insert cur steps.size
  let edges := ltsMap.getD cur #[]
  if edges.isEmpty then
    return if steps.isEmpty then #[] else #[steps]
  let mut allPaths : Array (Array GrammarSym) := #[]
  for t in edges do
    let combinedGuard : CharClass := match accGuard, t.label with
      | .empty, _ | _, .empty => .empty
      | .any, l => l
      | g, .any => g
      | g, l => (CharClass.conj g l).simplify
    if combinedGuard == .empty then
      continue
    match funcEntries.get? t.tgt with
    | some "_exit" => pure ()
    | some callee =>
      -- External call: classify using accumulated guard
      let sym := if callee == lexerName then
          GrammarSym.terminal combinedGuard
        else
          -- Decision 1: positive tokenCode guard → emit terminal instead of NT
          match combinedGuard.isPositiveTokenCode with
          | some _ => GrammarSym.terminal combinedGuard
          | none => GrammarSym.nonterminal callee
      let steps' := steps.push sym
      let retAddr := bodyBranches.findSome? fun b =>
        match extractRipGuard Amd64Reg.rip b.pc, extractRipTarget Amd64Reg.rip b.sub with
        | some src, some tgt =>
          if src == cur && tgt == t.tgt then extractCallReturn b.sub.mem else none
        | _, _ => none
      match retAddr with
      | some ret =>
        if funcBlocks.contains ret then
          allPaths := allPaths.append
            (ltsExtractProds ret steps' .any ltsMap funcBlocks funcEntries visited' nodeStepIdx' funcName fuel' bodyBranches lexerName tokenNames)
        else
          allPaths := allPaths.push steps'
      | none =>
        allPaths := allPaths.push steps'
    | none =>
      if funcBlocks.contains t.tgt then
        allPaths := allPaths.append
          (ltsExtractProds t.tgt steps combinedGuard ltsMap funcBlocks funcEntries visited' nodeStepIdx' funcName fuel' bodyBranches lexerName tokenNames)
      else
        -- Unknown external (helper like printf): preserve guard through call
        let retAddr := bodyBranches.findSome? fun b =>
          match extractRipGuard Amd64Reg.rip b.pc, extractRipTarget Amd64Reg.rip b.sub with
          | some src, some tgt =>
            if src == cur && tgt == t.tgt then extractCallReturn b.sub.mem else none
          | _, _ => none
        match retAddr with
        | some ret =>
          if funcBlocks.contains ret then
            allPaths := allPaths.append
              (ltsExtractProds ret steps combinedGuard ltsMap funcBlocks funcEntries visited' nodeStepIdx' funcName fuel' bodyBranches lexerName tokenNames)
          else if !steps.isEmpty then
            allPaths := allPaths.push steps
        | none =>
          if !steps.isEmpty then
            allPaths := allPaths.push steps
  return allPaths

/-- BFS reachability in LTS (for finding orphan blocks). -/
def ltsReachable (entry : UInt64)
    (ltsMap : Std.HashMap UInt64 (Array LTSTransition))
    (funcBlocks : Std.HashSet UInt64)
    (_funcEntries : Std.HashMap UInt64 String)
    (bodyBranches : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg))) :
    Std.HashSet UInt64 := Id.run do
  let mut visited : Std.HashSet UInt64 := {}
  let mut queue : Array UInt64 := #[entry]
  while !queue.isEmpty do
    let cur := queue.back!
    queue := queue.pop
    if visited.contains cur then pure ()
    else
      visited := visited.insert cur
      for t in ltsMap.getD cur #[] do
        if funcBlocks.contains t.tgt && !visited.contains t.tgt then
          queue := queue.push t.tgt
        else
          let retAddr := bodyBranches.findSome? fun b =>
            match extractRipGuard Amd64Reg.rip b.pc, extractRipTarget Amd64Reg.rip b.sub with
            | some src, some tgt =>
              if src == cur && tgt == t.tgt then extractCallReturn b.sub.mem else none
            | _, _ => none
          match retAddr with
          | some ret =>
            if funcBlocks.contains ret && !visited.contains ret then
              queue := queue.push ret
          | none => pure ()
  return visited

/-- Render a GrammarSym as a string using the token name table. -/
def renderSym (tokenNames : TokenNameTable) : GrammarSym → String
  | .terminal cc => charClassToTokenName tokenNames cc
  | .nonterminal name => name

/-- Format a production RHS as a space-separated string. -/
def formatProd (tokenNames : TokenNameTable) (syms : Array GrammarSym) : String :=
  if syms.isEmpty then "ε"
  else " ".intercalate (syms.toList.map (renderSym tokenNames))

/-- Extracted grammar for one NT: productions + optional repetition NT. -/
structure ExtractedNTGrammar where
  funcName : String
  prods : Array (Array GrammarSym)
  repNTName : Option String                          -- e.g., "statement_rep"
  repNTProds : Array (Array GrammarSym)              -- e.g., [statement], [statement, statement_rep]

/-- Extract grammar productions for one NT function.
    Returns productions + optional factored repetition NT. -/
def extractNTGrammar
    (funcName : String) (entryAddr : UInt64)
    (bodyArr : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)))
    (funcEntries : Std.HashMap UInt64 String)
    (lexerName : String := "next_sym")
    (tokenNames : TokenNameTable := {}) : ExtractedNTGrammar := Id.run do
  let ip_reg := Amd64Reg.rip
  let lts := extractLTS ip_reg bodyArr funcEntries
  let mut ltsMap : Std.HashMap UInt64 (Array LTSTransition) := {}
  let mut funcBlocks : Std.HashSet UInt64 := {}
  for b in bodyArr do
    match extractRipGuard ip_reg b.pc with
    | some src => funcBlocks := funcBlocks.insert src
    | none => pure ()
  for t in lts.transitions do
    let arr := ltsMap.getD t.src #[]
    ltsMap := ltsMap.insert t.src (arr.push t)
  -- Main DFS from entry
  let rawPaths := ltsExtractProds entryAddr #[] .any ltsMap funcBlocks funcEntries {} {} funcName 61 bodyArr lexerName tokenNames
  -- Orphan blocks: not reachable from entry, contain NT calls
  let reachable := ltsReachable entryAddr ltsMap funcBlocks funcEntries bodyArr
  let mut orphanPaths : Array (Array GrammarSym) := #[]
  for (src, edges) in ltsMap.toArray do
    if reachable.contains src then pure ()
    else
      for t in edges do
        match funcEntries.get? t.tgt with
        | some "_exit" => pure ()
        | some callee =>
          if callee == lexerName then pure ()
          else
            let retAddr := bodyArr.findSome? fun b =>
              match extractRipGuard ip_reg b.pc, extractRipTarget ip_reg b.sub with
              | some s, some tgt =>
                if s == src && tgt == t.tgt then extractCallReturn b.sub.mem else none
              | _, _ => none
            match retAddr with
            | some ret =>
              if funcBlocks.contains ret then
                orphanPaths := orphanPaths.append
                  (ltsExtractProds ret #[.nonterminal callee] .any ltsMap funcBlocks funcEntries {} {} funcName 61 bodyArr lexerName tokenNames)
            | none => pure ()
        | none => pure ()
  -- Deduplicate using rendered strings
  let mut seen : Std.HashSet String := {}
  let mut deduped : Array (Array GrammarSym) := #[]
  for p in rawPaths.append orphanPaths do
    let key := formatProd tokenNames p
    if !seen.contains key then
      seen := seen.insert key
      deduped := deduped.push p
  -- Post-process: factor self-repetition into repetition NT.
  -- Detect pattern: [funcName, funcName] production (self-recursive loop body)
  -- paired with a two-terminal production [T1, T2] (delimiter frame).
  -- Merge into: [T1, repNT, T2] with repNT → funcName | funcName repNT.
  let hasSelfRep := deduped.any fun p =>
    p.size == 2 && p[0]! == .nonterminal funcName && p[1]! == .nonterminal funcName
  if hasSelfRep then
    let repName := funcName ++ "_rep"
    let repProds : Array (Array GrammarSym) := #[
      #[.nonterminal funcName],
      #[.nonterminal funcName, .nonterminal repName]
    ]
    let isTwoTerminals (p : Array GrammarSym) : Bool :=
      p.size == 2 && p[0]!.isTerminal && p[1]!.isTerminal
    let modified := deduped.filterMap fun p =>
      if p.size == 2 && p[0]! == .nonterminal funcName && p[1]! == .nonterminal funcName then
        none
      else if isTwoTerminals p then
        some #[p[0]!, .nonterminal repName, p[1]!]
      else some p
    return { funcName := funcName, prods := modified, repNTName := some repName, repNTProds := repProds }
  else
    return { funcName := funcName, prods := deduped, repNTName := none, repNTProds := #[] }

/-- Structural comparison of extracted grammar against golden grammar.
    Builds terminal and NT mappings, then checks production-level isomorphism. -/
def structuralGoldenCompare (log : String → IO Unit)
    (grammars : Array ExtractedNTGrammar)
    (tokenNames : TokenNameTable)
    (golden : Std.HashMap String (List (List String)) := goldenProds) : IO Unit := do
  -- Collect all known NT names (function NTs + synthetic rep NTs)
  let mut allNTNames : Std.HashSet String := {}
  for g in grammars do
    allNTNames := allNTNames.insert g.funcName
    match g.repNTName with
    | some n => allNTNames := allNTNames.insert n
    | none => pure ()
  -- Golden NTs: keys of golden prods
  let goldenNTNames : Std.HashSet String :=
    golden.toArray.foldl (fun s (k, _) => s.insert k) {}
  for n in goldenNTNames do
    allNTNames := allNTNames.insert n
  -- Synthetic NTs: golden NTs not in extracted function NTs (e.g., "statements")
  let funcNTNames : Std.HashSet String :=
    grammars.foldl (fun s g => s.insert g.funcName) {}
  let syntheticGoldenNTs := goldenNTNames.toArray.filter fun n => !funcNTNames.contains n
  -- Map synthetic rep NTs to golden synthetic NTs
  let repNTs := grammars.filterMap fun g => g.repNTName
  let mut ntMapping : Std.HashMap String String := {}
  for i in [:repNTs.size.min syntheticGoldenNTs.size] do
    ntMapping := ntMapping.insert repNTs[i]! syntheticGoldenNTs[i]!
  -- Helper: check if a symbol name is a known NT (not a terminal)
  let isNT (name : String) : Bool := allNTNames.contains name
  -- Build terminal mapping by scanning UNMATCHED productions only.
  -- First remove exact matches, then build mappings from remaining pairs.
  let mut termMapping : Std.HashMap String String := {}
  let mut prodGoldenPairs : Array (Array (Array GrammarSym) × List (List String)) := #[]
  for g in grammars do
    prodGoldenPairs := prodGoldenPairs.push (g.prods, golden.getD g.funcName [])
    match g.repNTName with
    | some repName =>
      let goldenName := ntMapping.getD repName repName
      prodGoldenPairs := prodGoldenPairs.push (g.repNTProds, golden.getD goldenName [])
    | none => pure ()
  for (prods, goldenEntry) in prodGoldenPairs do
    -- Phase 1: remove exact matches from both pools
    let mut remainGolden : List (List String) := goldenEntry
    let mut unmatchedProds : Array (Array GrammarSym) := #[]
    for prod in prods do
      let rendered := prod.toList.map fun sym => match sym with
        | .terminal cc => charClassToTokenName tokenNames cc
        | .nonterminal n => ntMapping.getD n n
      let renderedStr := " ".intercalate rendered
      let exactMatch := remainGolden.any fun gp => " ".intercalate gp == renderedStr
      if exactMatch then
        remainGolden := remainGolden.filter fun gp => " ".intercalate gp != renderedStr
      else
        unmatchedProds := unmatchedProds.push prod
    -- Phase 2: build mappings from unmatched pairs
    for prod in unmatchedProds do
      let rendered := prod.toList.map fun sym => match sym with
        | .terminal cc => charClassToTokenName tokenNames cc
        | .nonterminal n => ntMapping.getD n n
      for gProd in remainGolden do
        if rendered.length == gProd.length then
          let pairs := rendered.zip gProd
          let allMatch := pairs.all fun (e, g) =>
            e == g || (!isNT e && !isNT g)
          if allMatch then
            for (e, g) in pairs do
              if e != g && !isNT e && !isNT g then
                termMapping := termMapping.insert e g
  -- Apply both mappings and count matches
  log "\n=== Structural Grammar Comparison ==="
  if !termMapping.isEmpty then
    let termPairs := termMapping.toArray.map fun (e, g) => s!"{e} ↔ {g}"
    log s!"  Terminal mapping: {", ".intercalate termPairs.toList}"
  if !ntMapping.isEmpty then
    let ntPairs := ntMapping.toArray.map fun (e, g) => s!"{e} ↔ {g}"
    log s!"  NT mapping: {", ".intercalate ntPairs.toList}"
  let mut totalMatch : Nat := 0
  let mut totalGolden : Nat := 0
  let mut totalExtra : Nat := 0
  for g in grammars do
    let goldenForFunc := golden.getD g.funcName []
    let goldenSet : Std.HashSet String :=
      goldenForFunc.foldl (fun s gp => s.insert (" ".intercalate gp)) {}
    -- Render extracted productions with mappings applied
    let mut matchCount : Nat := 0
    let mut extraCount : Nat := 0
    for prod in g.prods do
      let rendered := prod.toList.map fun sym => match sym with
        | .terminal cc =>
          let raw := charClassToTokenName tokenNames cc
          termMapping.getD raw raw
        | .nonterminal n => ntMapping.getD n n
      let renderedStr := " ".intercalate rendered
      if goldenSet.contains renderedStr then
        matchCount := matchCount + 1
      else
        extraCount := extraCount + 1
    -- Also check rep NT productions
    match g.repNTName with
    | some repName =>
      let goldenName := ntMapping.getD repName repName
      let repGolden := golden.getD goldenName []
      let repGoldenSet : Std.HashSet String :=
        repGolden.foldl (fun s gp => s.insert (" ".intercalate gp)) {}
      let mut repMatch : Nat := 0
      for prod in g.repNTProds do
        let rendered := prod.toList.map fun sym => match sym with
          | .terminal cc =>
            let raw := charClassToTokenName tokenNames cc
            termMapping.getD raw raw
          | .nonterminal n => ntMapping.getD n n
        let renderedStr := " ".intercalate rendered
        if repGoldenSet.contains renderedStr then
          repMatch := repMatch + 1
      let repTotal := repGolden.length
      let mark := if repMatch == repTotal && repTotal > 0 then " ✓" else ""
      log s!"  {repName} ({goldenName}): {repMatch}/{repTotal}{mark}"
      totalMatch := totalMatch + repMatch
      totalGolden := totalGolden + repTotal
    | none => pure ()
    let mark := if matchCount == goldenForFunc.length && goldenForFunc.length > 0 then " ✓" else ""
    log s!"  {g.funcName}: {matchCount}/{goldenForFunc.length}{mark}"
    if extraCount > 0 then
      log s!"    ({extraCount} extra productions)"
    totalMatch := totalMatch + matchCount
    totalGolden := totalGolden + goldenForFunc.length
    totalExtra := totalExtra + extraCount
  let mark := if totalMatch == totalGolden then " ✓" else ""
  log s!"  Total: {totalMatch}/{totalGolden}{mark}"
  if totalExtra > 0 then
    log s!"  ({totalExtra} extra productions total)"

/-! ## Name-Independent Structural Grammar Comparison (V2) -/

/-- Arity fingerprint for a non-terminal: (number_of_productions, sorted list of production lengths).
    Used as a cheap pre-filter: only NTs with identical fingerprints can possibly match. -/
structure ArityFingerprint where
  numProds : Nat
  sortedLengths : List Nat
  deriving BEq, Hashable, Inhabited, Repr

/-- Compute the arity fingerprint for a list of productions (each production is a list of symbols). -/
def arityFingerprint (prods : List (List String)) : ArityFingerprint :=
  let lengths := prods.map (·.length)
  { numProds := prods.length
    sortedLengths := lengths.mergeSort (· ≤ ·) }

/-- A flattened grammar: NT name → list of productions, each production a list of symbol strings.
    Both extracted and golden grammars get normalized into this form. -/
abbrev FlatGrammar := Std.HashMap String (List (List String))

/-- Flatten an extracted grammar array into a FlatGrammar, rendering symbols to strings. -/
def flattenExtracted (grammars : Array ExtractedNTGrammar) (tokenNames : TokenNameTable) :
    FlatGrammar := Id.run do
  let mut result : FlatGrammar := {}
  for g in grammars do
    let prods := g.prods.toList.map fun prod =>
      prod.toList.map fun sym => renderSym tokenNames sym
    result := result.insert g.funcName prods
    match g.repNTName with
    | some repName =>
      let repProds := g.repNTProds.toList.map fun prod =>
        prod.toList.map fun sym => renderSym tokenNames sym
      result := result.insert repName repProds
    | none => pure ()
  result

/-- Classify a symbol as terminal or non-terminal within a grammar context.
    A symbol is an NT if it appears as a key in the grammar. -/
def symIsNT (sym : String) (grammarKeys : Std.HashSet String) : Bool :=
  grammarKeys.contains sym

/-- Abstractly classify a symbol within a production: either as "NT-ref" or "terminal-leaf".
    Returns (isNT, symbolName). -/
structure SymClass where
  isNT : Bool
  name : String
  deriving BEq, Hashable, Inhabited

/-- Classify symbols in a production given the grammar's NT set. -/
def classifyProd (prod : List String) (ntSet : Std.HashSet String) : List SymClass :=
  prod.map fun sym => { isNT := ntSet.contains sym, name := sym }

/-- Check if two productions are structurally compatible: same length, same NT/terminal pattern.
    Returns a list of (extractedSym, goldenSym) pairs for all positions if compatible. -/
def productionsCompatible (extProd goldenProd : List SymClass) : Option (List (SymClass × SymClass)) :=
  if extProd.length != goldenProd.length then none
  else
    let pairs := extProd.zip goldenProd
    let allCompatible := pairs.all fun (e, g) => e.isNT == g.isNT
    if allCompatible then some pairs else none

/-- Attempt to match two productions under a (partial) symbol map.
    Returns an updated map if consistent, or none if there's a conflict.
    The map sends extracted symbol names to golden symbol names. -/
def matchProductionUnderMap (extProd goldenProd : List String)
    (extNTs goldenNTs : Std.HashSet String)
    (symMap : Std.HashMap String String) :
    Option (Std.HashMap String String) := Id.run do
  if extProd.length != goldenProd.length then return none
  let mut m := symMap
  for (eSym, gSym) in extProd.zip goldenProd do
    let eIsNT := extNTs.contains eSym
    let gIsNT := goldenNTs.contains gSym
    -- Both must be same class (both NT or both terminal)
    if eIsNT != gIsNT then return none
    -- Check consistency with existing map
    match m.get? eSym with
    | some existing =>
      if existing != gSym then return none
    | none =>
      -- Check no other extracted symbol maps to this golden symbol (injectivity)
      let conflict := m.toArray.any fun (_, v) => v == gSym
      if conflict then return none
      m := m.insert eSym gSym
  return some m

/-- Score for matching a single NT pair: counts how many productions match under a renaming. -/
structure NTMatchScore where
  matched : Nat     -- number of golden productions matched
  total : Nat       -- total golden productions
  extraExt : Nat    -- extracted productions with no golden match
  deriving Inhabited

/-- Try to match two sets of productions under a symbol map, returning the best score and updated map. -/
def scoreNTMatch (extProds goldenProds : List (List String))
    (extNTs goldenNTs : Std.HashSet String)
    (symMap : Std.HashMap String String) :
    NTMatchScore × Std.HashMap String String := Id.run do
  let mut m := symMap
  let mut matched : Nat := 0
  let mut usedGolden : Std.HashSet Nat := {}
  let goldenArr := goldenProds.toArray
  -- Greedy: for each extracted production, try to find a matching golden production
  for eProd in extProds do
    let mut foundMatch := false
    for idx in [:goldenArr.size] do
      if usedGolden.contains idx then continue
      match matchProductionUnderMap eProd goldenArr[idx]! extNTs goldenNTs m with
      | some newMap =>
        m := newMap
        matched := matched + 1
        usedGolden := usedGolden.insert idx
        foundMatch := true
        break
      | none => continue
    if !foundMatch then pure ()
  let extraExt := extProds.length - matched
  return ({ matched := matched, total := goldenProds.length, extraExt := extraExt }, m)

/-- Result of the full structural comparison. -/
structure StructuralCompareResult where
  /-- Mapping from extracted NT names to golden NT names. -/
  ntAlignment : List (String × String)
  /-- Per-NT match scores. -/
  perNT : List (String × String × NTMatchScore)
  /-- Total matched productions across all NTs. -/
  totalMatched : Nat
  /-- Total golden productions across all NTs. -/
  totalGolden : Nat
  /-- Extracted NTs that could not be mapped. -/
  unmappedExtracted : List String
  /-- Golden NTs that could not be mapped. -/
  unmappedGolden : List String
  /-- The final symbol map (terminals + NTs). -/
  symMap : Std.HashMap String String
  deriving Inhabited

/-- Check if two sorted length lists are compatible allowing a per-production offset of at most `maxDelta`.
    Each extracted length can be up to maxDelta larger than the corresponding golden length.
    Lists must have the same length. -/
def lengthsCompatible (extLengths goldenLengths : List Nat) (maxDelta : Nat := 1) : Bool :=
  if extLengths.length != goldenLengths.length then false
  else
    let pairs := extLengths.zip goldenLengths
    pairs.all fun (e, g) =>
      -- Allow extracted to be 0 to maxDelta larger than golden
      e >= g && e <= g + maxDelta

/-- Phase 1: compute candidate NT pairs based on arity fingerprints.
    Uses flexible matching: same number of productions, and sorted production lengths
    are compatible allowing a per-production offset (accounting for systematic `token` inflation). -/
def fingerprintCandidates (extGrammar goldenGrammar : FlatGrammar) :
    List (String × String) := Id.run do
  let mut candidates : List (String × String) := []
  let extEntries := extGrammar.toArray
  let goldenEntries := goldenGrammar.toArray
  for (eName, eProds) in extEntries do
    let eFP := arityFingerprint eProds
    for (gName, gProds) in goldenEntries do
      let gFP := arityFingerprint gProds
      -- Exact match or flexible match (same prod count, lengths within +1)
      if eFP == gFP ||
         (eFP.numProds == gFP.numProds &&
          lengthsCompatible eFP.sortedLengths gFP.sortedLengths) then
        candidates := candidates ++ [(eName, gName)]
  candidates

/-- Compare two match candidates: prefer higher match ratio, breaking ties by absolute count.
    Returns true if (m1, t1) is strictly better than (m2, t2).
    Uses cross-multiplication to avoid floating point: m1/t1 > m2/t2 iff m1*t2 > m2*t1. -/
def betterMatchScore (m1 t1 m2 t2 : Nat) : Bool :=
  -- Treat 0/0 as worse than any positive match
  if m1 == 0 && m2 == 0 then false
  else if m1 == 0 then false
  else if m2 == 0 then true
  else
    let cross1 := m1 * (if t2 == 0 then 1 else t2)
    let cross2 := m2 * (if t1 == 0 then 1 else t1)
    cross1 > cross2 || (cross1 == cross2 && m1 > m2)

/-- Phase 2: greedy bipartite matching of NT pairs.
    Iteratively pick the best-scoring unmatched (extracted, golden) pair.
    Prefers higher match ratio (matched/total), then absolute count as tiebreaker.
    The symbol map is built incrementally as NTs get matched. -/
def greedyNTAlignment (extGrammar goldenGrammar : FlatGrammar)
    (candidates : List (String × String)) :
    StructuralCompareResult := Id.run do
  let extNTs : Std.HashSet String := extGrammar.toArray.foldl (fun s (k, _) => s.insert k) {}
  let goldenNTs : Std.HashSet String := goldenGrammar.toArray.foldl (fun s (k, _) => s.insert k) {}
  let mut sMap : Std.HashMap String String := {}
  let mut matchedExt : Std.HashSet String := {}
  let mut matchedGolden : Std.HashSet String := {}
  let mut alignment : List (String × String) := []
  let mut perNT : List (String × String × NTMatchScore) := []
  let mut totalMatched : Nat := 0
  let mut totalGolden : Nat := 0
  -- Iterate: pick the best unmatched pair each round (prefer highest match ratio)
  let mut changed := true
  let mut fuel := candidates.length + 1
  while changed && fuel > 0 do
    fuel := fuel - 1
    changed := false
    let mut bestMatched : Nat := 0
    let mut bestTotal : Nat := 0
    let mut bestPair : Option (String × String) := none
    let mut bestMap : Std.HashMap String String := sMap
    let mut bestNTScore : NTMatchScore := { matched := 0, total := 0, extraExt := 0 }
    for (eName, gName) in candidates do
      if matchedExt.contains eName || matchedGolden.contains gName then continue
      let eProds := extGrammar.getD eName []
      let gProds := goldenGrammar.getD gName []
      let fullMap := sMap.insert eName gName
      let (score, newMap) := scoreNTMatch eProds gProds extNTs goldenNTs fullMap
      if score.matched > 0 && betterMatchScore score.matched score.total bestMatched bestTotal then
        bestMatched := score.matched
        bestTotal := score.total
        bestPair := some (eName, gName)
        bestMap := newMap
        bestNTScore := score
    match bestPair with
    | some (eName, gName) =>
      sMap := bestMap
      matchedExt := matchedExt.insert eName
      matchedGolden := matchedGolden.insert gName
      alignment := alignment ++ [(eName, gName)]
      perNT := perNT ++ [(eName, gName, bestNTScore)]
      totalMatched := totalMatched + bestNTScore.matched
      totalGolden := totalGolden + bestNTScore.total
      changed := true
    | none => pure ()
  -- After greedy alignment, try unmatched NTs with relaxed criteria.
  -- Require at least 2 matched productions or 100% of a small golden NT to accept.
  for (eName, _) in extGrammar.toArray do
    if matchedExt.contains eName then continue
    let eProds := extGrammar.getD eName []
    let mut bestMatched : Nat := 0
    let mut bestTotal : Nat := 0
    let mut bestGName : Option String := none
    let mut bestRen := sMap
    let mut bestNTScore : NTMatchScore := { matched := 0, total := 0, extraExt := 0 }
    for (gName, _gProds) in goldenGrammar.toArray do
      if matchedGolden.contains gName then continue
      let gProds := goldenGrammar.getD gName []
      let fullMap := sMap.insert eName gName
      let (score, newMap) := scoreNTMatch eProds gProds extNTs goldenNTs fullMap
      -- Quality gate: require ≥50% golden coverage, or all golden prods matched
      let acceptable := score.matched > 0 &&
        (score.matched * 2 >= score.total || score.matched == score.total)
      if acceptable && betterMatchScore score.matched score.total bestMatched bestTotal then
        bestMatched := score.matched
        bestTotal := score.total
        bestGName := some gName
        bestRen := newMap
        bestNTScore := score
    if bestMatched > 0 then
      match bestGName with
      | some gName =>
        sMap := bestRen
        matchedExt := matchedExt.insert eName
        matchedGolden := matchedGolden.insert gName
        alignment := alignment ++ [(eName, gName)]
        perNT := perNT ++ [(eName, gName, bestNTScore)]
        totalMatched := totalMatched + bestNTScore.matched
        totalGolden := totalGolden + bestNTScore.total
      | none => pure ()
  let unmappedExt := extGrammar.toArray.toList.filterMap fun (k, _) =>
    if matchedExt.contains k then none else some k
  let unmappedGolden := goldenGrammar.toArray.toList.filterMap fun (k, _) =>
    if matchedGolden.contains k then none else some k
  -- Add unmatched golden NTs to total count
  for (gName, _) in goldenGrammar.toArray do
    if !matchedGolden.contains gName then
      totalGolden := totalGolden + (goldenGrammar.getD gName []).length
  { ntAlignment := alignment
    perNT := perNT
    totalMatched := totalMatched
    totalGolden := totalGolden
    unmappedExtracted := unmappedExt
    unmappedGolden := unmappedGolden
    symMap := sMap }

/-- Name-independent structural grammar comparison.
    Unlike structuralGoldenCompare which matches by NT name, this compares grammar structure
    by finding the best alignment between extracted and golden NTs based on production shapes. -/
def structuralGoldenCompareV2 (log : String → IO Unit)
    (grammars : Array ExtractedNTGrammar)
    (tokenNames : TokenNameTable)
    (golden : Std.HashMap String (List (List String)) := goldenProds) : IO Unit := do
  -- Flatten extracted grammar
  let extGrammar := flattenExtracted grammars tokenNames
  -- Phase 1: arity fingerprint pre-filter
  let candidates := fingerprintCandidates extGrammar golden
  -- Phase 2: greedy bipartite matching
  let result := greedyNTAlignment extGrammar golden candidates
  -- Report results
  log "\n=== Structural Grammar Comparison V2 (name-independent) ==="
  log s!"  Fingerprint candidates: {candidates.length} pairs from {extGrammar.size} extracted × {golden.size} golden NTs"
  if result.ntAlignment.isEmpty then
    log "  No structural NT matches found."
  else
    log s!"  NT alignment ({result.ntAlignment.length} pairs):"
    for (eName, gName) in result.ntAlignment do
      log s!"    {eName} ↔ {gName}"
  -- Per-NT scores
  for (eName, gName, score) in result.perNT do
    let mark := if score.matched == score.total && score.total > 0 then " ✓" else ""
    let extraStr := if score.extraExt > 0 then s!" (+{score.extraExt} extra)" else ""
    log s!"    {eName} ↔ {gName}: {score.matched}/{score.total}{mark}{extraStr}"
  -- Symbol map (terminal mappings only, not NTs)
  let termMappings := result.symMap.toArray.filter fun (k, _) =>
    !(extGrammar.toArray.any fun (eName, _) => eName == k)
  if !termMappings.isEmpty then
    let termPairs := termMappings.map fun (e, g) => s!"{e} ↔ {g}"
    log s!"  Terminal mapping: {", ".intercalate termPairs.toList}"
  -- Unmapped NTs
  if !result.unmappedExtracted.isEmpty then
    log s!"  Unmapped extracted NTs: {", ".intercalate result.unmappedExtracted}"
  if !result.unmappedGolden.isEmpty then
    log s!"  Unmapped golden NTs: {", ".intercalate result.unmappedGolden}"
  -- Total score (only over matched golden NTs, not all golden NTs)
  let matchedGoldenTotal := result.perNT.foldl (fun acc (_, _, s) => acc + s.total) 0
  let mark := if result.totalMatched == matchedGoldenTotal && matchedGoldenTotal > 0 then " ✓" else ""
  log s!"  Matched: {result.totalMatched}/{matchedGoldenTotal} productions (across {result.ntAlignment.length} NT pairs){mark}"
  log s!"  Coverage: {result.ntAlignment.length}/{golden.size} golden NTs aligned"

/-- Print EBNF grammar for all NT functions using LTS-based extraction.
    Uses ParserStructure for lexer identification and token names when available. -/
def printLTSGrammar (log : String → IO Unit)
    (functions : Array FunctionSpec)
    (funcEntries : Std.HashMap UInt64 String)
    (_summaries : Std.HashMap UInt64 (Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg))))
    (parserStructure : Option ParserStructure := none)
    (golden : Std.HashMap String (List (List String)) := goldenProds) : IO Unit := do
  let ip_reg := Amd64Reg.rip
  let (tokenNames, lexerName, lexerAddr) := match parserStructure with
    | some ps => (ps.tokenNames, ps.lexerName, ps.lexerAddr)
    | none => (({} : TokenNameTable), "next_sym", (0 : UInt64))
  log s!"\n=== Token Name Table ({tokenNames.size} entries, derived={parserStructure.isSome}) ==="
  for (code, name) in tokenNames.toArray do
    log s!"  {code.toNat} → {name}"
  -- Extract grammar for detected NT classifiers (or all non-lexer if no ParserStructure)
  let classifierAddrs : Option (Std.HashSet UInt64) := match parserStructure with
    | some ps => some (ps.classifiers.foldl (fun s f => s.insert f.entryAddr) {})
    | none => none
  let mut grammars : Array ExtractedNTGrammar := #[]
  for func in functions do
    if func.entryAddr == lexerAddr then continue
    -- When parser structure detected, only extract for classifier NTs
    match classifierAddrs with
    | some addrs => if !addrs.contains func.entryAddr then continue
    | none => pure ()
    -- Skip lexer by name for backward compatibility when no ParserStructure
    if parserStructure.isNone && func.name == "next_sym" then continue
    match parseBlocksWithAddresses func.blocks with
    | .error e => log s!"  Parse error for {func.name}: {e}"
    | .ok pairs =>
      let bodyArr := flatBodyDenotArray ip_reg pairs
      grammars := grammars.push (extractNTGrammar func.name func.entryAddr bodyArr funcEntries lexerName tokenNames)
  -- Print raw extracted grammar
  log "\n=== EBNF Grammar (LTS-based extraction) ==="
  for g in grammars do
    log s!"\n  {g.funcName}:"
    for prod in g.prods do
      log s!"    {g.funcName} -> {formatProd tokenNames prod}"
    match g.repNTName with
    | some repName =>
      log s!"    -- Repetition NT: {repName}"
      for prod in g.repNTProds do
        log s!"    {repName} -> {formatProd tokenNames prod}"
    | none => pure ()
  -- Structural comparison against golden grammar
  structuralGoldenCompare log grammars tokenNames golden
  -- Name-independent structural comparison (V2)
  structuralGoldenCompareV2 log grammars tokenNames golden

