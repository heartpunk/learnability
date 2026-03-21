import Instances.ISAs.DispatchLoopWTO
import Instances.ISAs.DispatchLoopGrammar

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA VexIRParser

/-! ## Generic Dispatch Table Extraction

Extract dispatch structure from converged summaries as a domain-independent
intermediate representation. Each function's behavior is decomposed into
dispatch groups keyed by equality comparisons in the PC guards.

This feeds into domain-specific interpretation layers (grammar, state machine,
opsem) and can be wrapped as a Cslib.LTS for formal simulation/bisimulation. -/

/-- Extract all eq(expr, const) comparisons from a PC guard.
    Returns the expression being compared and the constant value. -/
def extractComparisons {Reg : Type} : SymPC Reg → Array (SymExpr Reg × UInt64)
  | .eq e (.const v) => #[(e, v)]
  | .eq (.const v) e => #[(e, v)]
  | .and φ ψ => extractComparisons φ ++ extractComparisons ψ
  | _ => #[]

/-- A dispatch key: the full tuple of equality comparisons from a branch's PC.
    For a parser: [(rax, 5)]. For a type system: [(node_tag, 3), (subtype_tag, 7)].
    For a state machine: [(state_var, 2), (input_byte, 0x1B)]. -/
structure DispatchKey where
  comparisons : Array (SymExpr Amd64Reg × UInt64)
  deriving Inhabited

instance : BEq DispatchKey where
  beq a b := a.comparisons == b.comparisons

instance : Hashable DispatchKey where
  hash dk := dk.comparisons.foldl (fun acc (e, v) => mixHash acc (mixHash (hash e) (hash v))) 0

/-- A group of branches sharing the same dispatch key. -/
structure BranchGroup where
  key : DispatchKey
  branches : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg))
  callTargets : Array UInt64  -- functions called within this group

/-- Per-function dispatch table. -/
structure FunctionDispatchTable where
  funcAddr : UInt64
  funcName : String
  groups : Array BranchGroup
  dimensions : Array (SymExpr Amd64Reg)  -- which expressions are dispatched on

/-- A generic LTS transition with effect metadata. -/
structure GenericLTSTransition where
  src : UInt64
  label : DispatchKey
  tgt : UInt64
  effects : Option (SymSub Amd64Reg)  -- what this transition does to state

/-- A generic extracted LTS: states are addresses, labels are dispatch keys. -/
structure GenericExtractedLTS where
  transitions : Array GenericLTSTransition
  states : Std.HashSet UInt64
  init : UInt64

/-- Extract dispatch table from a function's converged summary branches. -/
def extractDispatchTable (funcAddr : UInt64) (funcName : String)
    (branches : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg))) :
    FunctionDispatchTable := Id.run do
  let ip_reg := Amd64Reg.rip
  -- Group branches by dispatch key
  let mut groupMap : Std.HashMap UInt64 (DispatchKey × Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg))) := {}
  let mut allDims : Std.HashSet UInt64 := {}  -- hash of dimension exprs for dedup
  let mut dimList : Array (SymExpr Amd64Reg) := #[]
  for b in branches do
    let comps := extractComparisons b.pc
    -- Filter out rip-guard comparisons (structural routing, not dispatch)
    let dataComps := comps.filter fun (e, _) => match e with
      | .reg r => !(r == ip_reg)
      | _ => true
    let key : DispatchKey := ⟨dataComps⟩
    let h := hash key
    let (_, arr) := groupMap.getD h (key, #[])
    groupMap := groupMap.insert h (key, arr.push b)
    -- Collect dimensions
    for (e, _) in dataComps do
      let eh := hash e
      unless allDims.contains eh do
        allDims := allDims.insert eh
        dimList := dimList.push e
  -- Build groups with call targets
  let mut groups : Array BranchGroup := #[]
  for (_, (key, branchArr)) in groupMap.toArray do
    let mut targets : Std.HashSet UInt64 := {}
    for b in branchArr do
      match extractRipTarget ip_reg b.sub with
      | some tgt => targets := targets.insert tgt
      | none => pure ()
    groups := groups.push ⟨key, branchArr, targets.toArray⟩
  return ⟨funcAddr, funcName, groups, dimList⟩

/-- Construct a generic LTS from dispatch tables. -/
def constructLTS (funcAddr : UInt64)
    (branches : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg))) :
    GenericExtractedLTS := Id.run do
  let ip_reg := Amd64Reg.rip
  let mut transitions : Array GenericLTSTransition := #[]
  let mut states : Std.HashSet UInt64 := {}
  states := states.insert funcAddr
  for b in branches do
    let src := match extractRipGuard ip_reg b.pc with
      | some addr => addr
      | none => funcAddr
    let tgt := match extractRipTarget ip_reg b.sub with
      | some addr => addr
      | none => 0  -- unknown target
    let comps := extractComparisons b.pc
    let dataComps := comps.filter fun (e, _) => match e with
      | .reg r => !(r == ip_reg)
      | _ => true
    let key : DispatchKey := ⟨dataComps⟩
    states := states.insert src
    if tgt != 0 then states := states.insert tgt
    transitions := transitions.push ⟨src, key, tgt, some b.sub⟩
  return ⟨transitions, states, funcAddr⟩

/-! ## LTS Serialization -/

mutual
/-- Render a SymExpr as a compact s-expression string (human-readable, not SMT-LIB). -/
private def renderExpr : SymExpr Amd64Reg → String
  | .const v => hexAddr v
  | .reg r => s!"{r}"
  | .add64 a b => s!"(+ {renderExpr a} {renderExpr b})"
  | .sub64 a b => s!"(- {renderExpr a} {renderExpr b})"
  | .and64 a b => s!"(& {renderExpr a} {renderExpr b})"
  | .or64 a b => s!"(| {renderExpr a} {renderExpr b})"
  | .xor64 a b => s!"(^ {renderExpr a} {renderExpr b})"
  | .shl64 a b => s!"(<< {renderExpr a} {renderExpr b})"
  | .shr64 a b => s!"(>> {renderExpr a} {renderExpr b})"
  | .mul64 a b => s!"(* {renderExpr a} {renderExpr b})"
  | .low32 e => s!"(low32 {renderExpr e})"
  | .uext32 e => s!"(uext32 {renderExpr e})"
  | .sext8to32 e => s!"(sext8to32 {renderExpr e})"
  | .sext32to64 e => s!"(sext32to64 {renderExpr e})"
  | .not64 e => s!"(~ {renderExpr e})"
  | .load w m a => s!"(load{w.byteCount * 8} {renderMem m} {renderExpr a})"
  | .sub32 a b => s!"(sub32 {renderExpr a} {renderExpr b})"
  | .shl32 a b => s!"(shl32 {renderExpr a} {renderExpr b})"
  | .and32 a b => s!"(and32 {renderExpr a} {renderExpr b})"
  | .or32 a b => s!"(or32 {renderExpr a} {renderExpr b})"
  | .xor32 a b => s!"(xor32 {renderExpr a} {renderExpr b})"
  | .mul32 a b => s!"(mul32 {renderExpr a} {renderExpr b})"
  | .not32 e => s!"(not32 {renderExpr e})"
  | .sar64 a b => s!"(sar64 {renderExpr a} {renderExpr b})"
  | .sar32 a b => s!"(sar32 {renderExpr a} {renderExpr b})"
  | .ite c t f => s!"(ite {renderExpr c} {renderExpr t} {renderExpr f})"

private def renderMem : SymMem Amd64Reg → String
  | .base => "mem"
  | .store w m a v => s!"(store{w.byteCount * 8} {renderMem m} {renderExpr a} {renderExpr v})"
end

/-- Render a SymPC as a compact string. -/
private def renderPC : SymPC Amd64Reg → String
  | .true => "true"
  | .eq a b => s!"(= {renderExpr a} {renderExpr b})"
  | .lt a b => s!"(< {renderExpr a} {renderExpr b})"
  | .le a b => s!"(<= {renderExpr a} {renderExpr b})"
  | .and φ ψ => s!"(∧ {renderPC φ} {renderPC ψ})"
  | .not φ => s!"(¬ {renderPC φ})"

/-- Serialize a GenericExtractedLTS to JSON. -/
def GenericExtractedLTS.toJson (lts : GenericExtractedLTS)
    (funcName : String) (funcEntries : Std.HashMap UInt64 String) : Lean.Json :=
  let transJson := lts.transitions.map fun t =>
    let labelJson := Lean.Json.arr (t.label.comparisons.map fun (e, v) =>
      Lean.Json.mkObj [
        ("expr", .str (renderExpr e)),
        ("value", .num ⟨v.toNat, 0⟩),
        ("valueHex", .str (hexAddr v))
      ])
    let srcName := funcEntries.getD t.src (hexAddr t.src)
    let tgtName := funcEntries.getD t.tgt (hexAddr t.tgt)
    -- Render effects: just the register map (skip mem for size)
    let effectsJson := match t.effects with
      | some sub =>
        let regEffects := VexISA.EnumReg.allRegs.filterMap fun (r : Amd64Reg) =>
          let e := sub.regs r
          -- Skip identity mappings (reg r → reg r)
          match e with
          | .reg r' => if r == r' then none else some (s!"{r}", Lean.Json.str (renderExpr e))
          | _ => some (s!"{r}", Lean.Json.str (renderExpr e))
        Lean.Json.mkObj regEffects
      | none => .null
    Lean.Json.mkObj [
      ("src", .str (hexAddr t.src)),
      ("srcName", .str srcName),
      ("label", labelJson),
      ("tgt", .str (hexAddr t.tgt)),
      ("tgtName", .str tgtName),
      ("effects", effectsJson)
    ]
  let statesJson := Lean.Json.arr (lts.states.toArray.map fun s =>
    Lean.Json.mkObj [
      ("addr", .str (hexAddr s)),
      ("name", .str (funcEntries.getD s (hexAddr s)))
    ])
  Lean.Json.mkObj [
    ("function", .str funcName),
    ("init", .str (hexAddr lts.init)),
    ("stateCount", .num ⟨lts.states.size, 0⟩),
    ("transitionCount", .num ⟨lts.transitions.size, 0⟩),
    ("states", statesJson),
    ("transitions", Lean.Json.arr transJson)
  ]

/-- Write a GenericExtractedLTS to a JSON file. -/
def writeLTS (lts : GenericExtractedLTS) (funcName : String)
    (funcEntries : Std.HashMap UInt64 String) (dir : System.FilePath) : IO Unit := do
  let json := lts.toJson funcName funcEntries
  let path := dir / s!"{funcName}.lts.json"
  IO.FS.writeFile path json.pretty

/-! ## Run stabilization -/

/-- Build funcEntries map from function specs. -/
def buildFuncEntries (functions : Array FunctionSpec) : Std.HashMap UInt64 String :=
  functions.foldl (fun m f => m.insert f.entryAddr f.name) {}

/-- Run the full pipeline on a set of function specs: fixpoint → detect → extract.
    The generic pipeline used by both legacy and file-based entry points.
    When golden prods are provided, structural comparison is run against them. -/
def runPipeline (functions : Array FunctionSpec) (regions : Array MemRegion := #[])
    (log : String → IO Unit)
    (golden : Std.HashMap String (List (List String)) := goldenProds)
    (maxBranches : Nat := 10000)
    (diagnostics : Bool := false)
    (maxIter : Nat := 200) : IO Unit := do
  log "=== Stratified Dispatch Loop Stabilization ==="
  let summaries ← stratifiedFixpoint functions regions log (maxBranches := maxBranches) (diagnostics := diagnostics) (maxIter := maxIter)
  let funcEntries := buildFuncEntries functions
  -- Parser detection
  let parserResult ← detectParser functions summaries log
  let ps := match parserResult with
    | .ok ps => some ps
    | .error _ => none
  -- EBNF extraction for parser NTs (LTS-based)
  printLTSGrammar log functions funcEntries summaries ps golden

/-- Main entry point using file-based input: blocks.json + ELF binary.
    Loads blocks from JSON, reads symbols from ELF, discovers functions, runs pipeline. -/
def dispatchLoopEvalFromFiles (blocksJson : System.FilePath) (elfBinary : System.FilePath)
    (log : String → IO Unit) : IO Unit := do
  log s!"Loading blocks from {blocksJson}..."
  let blocks ← loadBlocksFromJSON blocksJson
  log s!"  {blocks.size} blocks loaded"
  log s!"Reading symbols from {elfBinary}..."
  let symbols ← ElfSymbolTable.readSymbolsFromFile elfBinary
  log s!"  {symbols.size} function symbols found"
  for (name, addr, size) in symbols do
    log s!"    {name} @ 0x{String.ofList (Nat.toDigits 16 addr.toNat)}, {size} bytes"
  match discoverFunctions blocks symbols with
  | .error e => log s!"Function discovery error: {e}"
  | .ok result =>
    log s!"Discovered {result.functions.size} functions with blocks:"
    for f in result.functions do
      log s!"  {f.name}: {f.blocks.length} blocks"
    if result.orphanCount > 0 then
      log s!"  WARNING: {result.orphanCount} blocks not in any function symbol range"
    runPipeline result.functions (log := log)

/-- Standard log function: writes to both stdout and a log file.
    Flushes stdout after each line to ensure output appears immediately
    even when stdout is redirected (e.g., in parallel runners). -/
def mkLogger (logPath : System.FilePath) : IO (String → IO Unit) := do
  IO.FS.writeFile logPath ""
  return fun msg => do
    IO.println msg
    (← IO.getStdout).flush
    let h ← IO.FS.Handle.mk logPath .append
    h.putStrLn msg

def mkFileLogger (logPath : System.FilePath) : IO (String → IO Unit) := do
  IO.FS.writeFile logPath ""
  return fun msg => do
    let h ← IO.FS.Handle.mk logPath .append
    h.putStrLn msg

/-! ## JSON Output -/

/-- Serialize extracted pipeline results to structured JSON.
    Includes: functions, parser structure, grammar, and LTS. -/
def pipelineToJson (functions : Array FunctionSpec)
    (parserStructure : Option ParserStructure) : Lean.Json :=
  let ip_reg := Amd64Reg.rip
  let (tokenNames, lexerName, lexerAddr) := match parserStructure with
    | some ps => (ps.tokenNames, ps.lexerName, ps.lexerAddr)
    | none => (({} : TokenNameTable), "next_sym", (0 : UInt64))
  let funcEntries := functions.foldl (fun m f => m.insert f.entryAddr f.name)
    ({} : Std.HashMap UInt64 String)
  -- Extract grammars (pure computation)
  let classifierAddrs : Option (Std.HashSet UInt64) := match parserStructure with
    | some ps => some (ps.classifiers.foldl (fun s f => s.insert f.entryAddr) {})
    | none => none
  let grammars : Array ExtractedNTGrammar := Id.run do
    let mut gs : Array ExtractedNTGrammar := #[]
    for func in functions do
      let skip := func.entryAddr == lexerAddr ||
        (parserStructure.isNone && func.name == "next_sym") ||
        (match classifierAddrs with | some addrs => !addrs.contains func.entryAddr | none => false)
      if !skip then
        match parseBlocksWithAddresses func.blocks with
        | .error _ => pure ()
        | .ok pairs =>
          let bodyArr := flatBodyDenotArray ip_reg pairs
          gs := gs.push (extractNTGrammar func.name func.entryAddr bodyArr funcEntries
                          lexerName tokenNames)
    gs
  -- Functions array
  let funcsJson := Lean.Json.arr (functions.map fun f =>
    Lean.Json.mkObj [
      ("name", .str f.name),
      ("entryAddr", .str (hexAddr f.entryAddr)),
      ("blockCount", .num ⟨f.blocks.length, 0⟩)
    ])
  -- Parser structure
  let parserJson := match parserStructure with
    | some ps => Lean.Json.mkObj [
        ("detected", .bool true),
        ("lexer", .str ps.lexerName),
        ("lexerAddr", .str (hexAddr ps.lexerAddr)),
        ("entryClassifier", .str (hexAddr ps.entryClassifier)),
        ("tokenNames", Lean.Json.mkObj (ps.tokenNames.toArray.toList.map fun (code, name) =>
          (s!"{code.toNat}", .str name)))
      ]
    | none => Lean.Json.mkObj [("detected", .bool false)]
  -- Grammar per NT
  let grammarEntries : List (String × Lean.Json) := Id.run do
    let mut entries : List (String × Lean.Json) := []
    for g in grammars do
      let prods := g.prods.map fun prod =>
        Lean.Json.arr (prod.map fun sym => .str (renderSym tokenNames sym))
      entries := entries ++ [(g.funcName, Lean.Json.mkObj [
        ("productions", Lean.Json.arr prods)
      ])]
      match g.repNTName with
      | some repName =>
        let repProds := g.repNTProds.map fun prod =>
          Lean.Json.arr (prod.map fun sym => .str (renderSym tokenNames sym))
        entries := entries ++ [(repName, Lean.Json.mkObj [
          ("productions", Lean.Json.arr repProds)
        ])]
      | none => pure ()
    entries
  let grammarJson := Lean.Json.mkObj grammarEntries
  -- LTS per NT function
  let ltsEntries : List (String × Lean.Json) := Id.run do
    let mut entries : List (String × Lean.Json) := []
    for g in grammars do
      match functions.find? (·.name == g.funcName) with
      | none => pure ()
      | some f =>
        match parseBlocksWithAddresses f.blocks with
        | .error _ => pure ()
        | .ok pairs =>
          let bodyArr := flatBodyDenotArray ip_reg pairs
          let lts := extractLTS ip_reg bodyArr funcEntries
          let transJson := lts.transitions.map fun t =>
            Lean.Json.mkObj [
              ("src", .str (hexAddr t.src)),
              ("label", .str (charClassToTokenName tokenNames t.label)),
              ("tgt", .str (hexAddr t.tgt))
            ]
          entries := entries ++ [(f.name, Lean.Json.mkObj [
            ("transitions", Lean.Json.arr transJson),
            ("stateCount", .num ⟨lts.states.size, 0⟩),
            ("transitionCount", .num ⟨lts.transitions.size, 0⟩)
          ])]
    entries
  let ltsJson := Lean.Json.mkObj ltsEntries
  -- Top-level result
  Lean.Json.mkObj [
    ("functions", funcsJson),
    ("parser", parserJson),
    ("grammar", grammarJson),
    ("lts", ltsJson)
  ]

/-- Run pipeline and output structured JSON to stdout. Log goes to file only. -/
def runPipelineJSON (functions : Array FunctionSpec) (regions : Array MemRegion := #[])
    (log : String → IO Unit)
    (maxBranches : Nat := 10000)
    (diagnostics : Bool := false)
    (maxIter : Nat := 200) : IO Unit := do
  log "=== Stratified Dispatch Loop Stabilization (JSON mode) ==="
  let summaries ← stratifiedFixpoint functions regions log (maxBranches := maxBranches) (diagnostics := diagnostics) (maxIter := maxIter)
  let parserResult ← detectParser functions summaries log
  let ps := match parserResult with
    | .ok ps => some ps
    | .error _ => none
  let json := pipelineToJson functions ps
  IO.println json.pretty

/-- Auto-detect WTO root: function with no incoming edges in the call graph.
    Falls back to a function named "main", then to the first function. -/
def autoDetectRoot (functions : Array FunctionSpec) (callGraph : Array (UInt64 × UInt64))
    (log : String → IO Unit) : IO UInt64 := do
  -- Try: function named "main"
  match functions.find? (·.name == "main") with
  | some f =>
    log s!"  auto-root: found 'main' @ {hexAddr f.entryAddr}"
    return f.entryAddr
  | none => pure ()
  -- Try: function not called by any other function
  let calledSet : Std.HashSet UInt64 := callGraph.foldl (fun s (_, tgt) => s.insert tgt) {}
  let roots := functions.filter fun f => !calledSet.contains f.entryAddr
  if roots.size == 1 then
    log s!"  auto-root: unique uncalled function '{roots[0]!.name}' @ {hexAddr roots[0]!.entryAddr}"
    return roots[0]!.entryAddr
  else if roots.size > 1 then
    log s!"  auto-root: {roots.size} uncalled functions, picking '{roots[0]!.name}'"
    return roots[0]!.entryAddr
  -- Fallback: first function
  log s!"  auto-root: all functions called, using first: '{functions[0]!.name}'"
  return functions[0]!.entryAddr

/-- Run pipeline using WTO-driven fixpoint: call graph → WTO → wtoFixpoint → detect → extract. -/
def runPipelineWTO (functions : Array FunctionSpec) (regions : Array MemRegion := #[])
    (log : String → IO Unit)
    (golden : Std.HashMap String (List (List String)) := goldenProds)
    (maxBranches : Nat := 10000)
    (diagnostics : Bool := false)
    (maxIter : Nat := 200)
    (entryAddr : Option UInt64 := none)
    (inputPath : Option System.FilePath := none) : IO Unit := do
  log "=== WTO Dispatch Loop Stabilization ==="
  -- Dedup functions by entry address: .localalias and other linker aliases
  -- produce multiple FunctionSpecs at the same address; keep first occurrence only.
  let mut seenAddrs : Std.HashSet UInt64 := {}
  let mut dedupFuncs : Array FunctionSpec := #[]
  for f in functions do
    unless seenAddrs.contains f.entryAddr do
      seenAddrs := seenAddrs.insert f.entryAddr
      dedupFuncs := dedupFuncs.push f
  if dedupFuncs.size < functions.size then
    log s!"  dedup: {functions.size} → {dedupFuncs.size} functions (removed {functions.size - dedupFuncs.size} aliases)"
  let functions := dedupFuncs
  -- Build call graph and compute WTO
  let callGraph ← buildCallGraph functions log
  let root ← match entryAddr with
    | some addr => pure addr
    | none => autoDetectRoot functions callGraph log
  let nodes := functions.map (·.entryAddr)
  let wto := computeWTO nodes callGraph root
  let nameOf (addr : UInt64) : String :=
    match functions.find? (·.entryAddr == addr) with
    | some f => f.name
    | none => hexAddr addr
  log s!"  WTO: {ppWTO wto nameOf}"
  -- Run WTO fixpoint
  let summaries ← wtoFixpoint functions wto regions log (maxIter := maxIter) (maxBranches := maxBranches) (diagnostics := diagnostics)
  let funcEntries := buildFuncEntries functions
  -- Build address classifier for label simplification (same as wtoFixpoint uses)
  let addrClassify : Option (AddrClassifier Amd64Reg) :=
    if regions.size > 0 then
      some (classifyAddr regions [Amd64Reg.rsp, Amd64Reg.rbp])
    else none
  -- Simplify all branch guard PCs for clean LTS labels.
  -- Subs are already simplified during stabilization; this pass resolves
  -- nested load-through-store chains in guard PCs (e.g.,
  -- load8(store64(store64(mem, rbp-X, ..), rbp-Y, ..), ptr+8) → load8(mem, ptr+8)).
  log s!"\n=== Label Simplification ==="
  let mut simplifiedSummaries : Std.HashMap UInt64 (Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg))) := {}
  let mut totalSimplified : Nat := 0
  let mut totalDropped : Nat := 0
  for func in functions do
    let branches := summaries.getD func.entryAddr #[]
    let simplified := branches.filterMap fun b => simplifyBranchFull b addrClassify
    simplifiedSummaries := simplifiedSummaries.insert func.entryAddr simplified
    totalSimplified := totalSimplified + simplified.size
    totalDropped := totalDropped + (branches.size - simplified.size)
  log s!"  {totalSimplified} branches simplified, {totalDropped} dropped (unsatisfiable after simplification)"
  -- Extract generic dispatch tables + LTS for each function
  log s!"\n=== Dispatch Table Extraction ==="
  let mut dispatchTables : Array FunctionDispatchTable := #[]
  let mut ltsMap : Std.HashMap UInt64 GenericExtractedLTS := {}
  for func in functions do
    let branches := simplifiedSummaries.getD func.entryAddr #[]
    if branches.size > 0 then
      let dt := extractDispatchTable func.entryAddr func.name branches
      let lts := constructLTS func.entryAddr branches
      dispatchTables := dispatchTables.push dt
      ltsMap := ltsMap.insert func.entryAddr lts
      log s!"  {func.name}: {dt.groups.size} dispatch groups, {dt.dimensions.size} dimensions, {lts.transitions.size} LTS transitions, {lts.states.size} states"
  -- Persist LTS to disk
  let ltsDir : System.FilePath := ".lake/lts"
  IO.FS.createDirAll ltsDir
  for func in functions do
    match ltsMap.get? func.entryAddr with
    | some lts => writeLTS lts func.name funcEntries ltsDir
    | none => pure ()
  log s!"  LTS written to {ltsDir}/"
  -- Grammar interpretation layer: identify lexer, classify functions, extract terminals
  log s!"\n=== Grammar Interpretation ==="
  let producers ← findProducers functions summaries log
  -- Find best producer (lexer): function with most distinct output values
  let lexerInfo := producers.foldl (fun best (addr, vals) =>
    match best with
    | none => some (addr, vals)
    | some (_, bestVals) => if vals.size > bestVals.size then some (addr, vals) else best)
    (none : Option (UInt64 × Array UInt64))
  let (lexerAddr, lexerName, tokenNames) ← match lexerInfo with
    | some (addr, _vals) =>
      let name := funcEntries.getD addr "unknown"
      log s!"  Lexer identified: {name} @ {hexAddr addr}"
      -- Build token name table from lexer's BODY branches (not projected summaries,
      -- which have zeroed memory and lose the token-writing stores)
      let lexerSpec := functions.find? (·.entryAddr == addr) |>.getD ⟨name, addr, []⟩
      let lexerBodyBranches := match parseBlocksWithAddresses lexerSpec.blocks with
        | .ok pairs => flatBodyDenotArray Amd64Reg.rip pairs
        | .error _ => #[]
      let tokenNameTable ← deriveTokenNames lexerSpec lexerBodyBranches log
      log s!"  Token names: {tokenNameTable.size} entries"
      pure (addr, name, tokenNameTable)
    | none =>
      log s!"  No lexer identified — grammar extraction will use raw dispatch keys"
      pure (0, "unknown", ({} : TokenNameTable))
  -- Classify functions by call-graph relationship to lexer
  -- Direct caller: has an edge to lexer in call graph → grammar NT
  -- Transitive: reaches lexer through other functions → wrapper
  -- None: never reaches lexer → helper
  let directCallsLexer := fun (caller : UInt64) => callGraph.any fun (s, t) => s == caller && t == lexerAddr
  -- BFS reachability for transitive check
  let reachesLexer := fun (start : UInt64) => Id.run do
    let mut visited : Std.HashSet UInt64 := {}
    let mut queue : Array UInt64 := #[start]
    while !queue.isEmpty do
      let cur := queue.back!
      queue := queue.pop
      if visited.contains cur then continue
      visited := visited.insert cur
      if cur == lexerAddr then return true
      for (src, tgt) in callGraph do
        if src == cur && !visited.contains tgt then
          queue := queue.push tgt
    return false
  let mut grammarNTs : Array FunctionSpec := #[]
  let mut wrappers : Array FunctionSpec := #[]
  let mut helpers : Array FunctionSpec := #[]
  for func in functions do
    if func.entryAddr == lexerAddr then continue
    if directCallsLexer func.entryAddr then
      grammarNTs := grammarNTs.push func
    else if reachesLexer func.entryAddr then
      wrappers := wrappers.push func
    else
      helpers := helpers.push func
  log s!"  Grammar NTs (direct lexer callers): {grammarNTs.map (·.name)}"
  log s!"  Wrappers (transitive): {wrappers.map (·.name)}"
  log s!"  Helpers (no lexer path): {helpers.map (·.name)}"
  -- Build ParserStructure for printLTSGrammar
  let parserStructure : Option ParserStructure :=
    if lexerAddr != 0 && grammarNTs.size > 0 then
      some {
        lexerAddr := lexerAddr
        lexerName := lexerName
        tokenNames := tokenNames
        classifiers := grammarNTs
        entryClassifier := grammarNTs[0]!.entryAddr
      }
    else none
  -- Load golden grammar and run extraction
  let goldenGrammar ← match inputPath with
    | some path => loadGoldenForSubject path log
    | none => pure golden
  printLTSGrammar log functions funcEntries summaries parserStructure goldenGrammar

/-- Run WTO pipeline with JSON output. -/
def runPipelineWTOJSON (functions : Array FunctionSpec) (regions : Array MemRegion := #[])
    (log : String → IO Unit)
    (maxBranches : Nat := 10000)
    (diagnostics : Bool := false)
    (maxIter : Nat := 200)
    (entryAddr : Option UInt64 := none) : IO Unit := do
  log "=== WTO Dispatch Loop Stabilization (JSON mode) ==="
  let callGraph ← buildCallGraph functions log
  let root ← match entryAddr with
    | some addr => pure addr
    | none => autoDetectRoot functions callGraph log
  let nodes := functions.map (·.entryAddr)
  let wto := computeWTO nodes callGraph root
  let _summaries ← wtoFixpoint functions wto regions log (maxIter := maxIter) (maxBranches := maxBranches) (diagnostics := diagnostics)
  let json := pipelineToJson functions none
  IO.println json.pretty

/-! ## Entry-point scoping -/

/-- BFS reachability from an entry address in a call graph. Pure computation. -/
def callGraphReachable (entryAddr : UInt64) (callGraph : Array (UInt64 × UInt64)) :
    Std.HashSet UInt64 := Id.run do
  let mut reachable : Std.HashSet UInt64 := {}
  let mut queue : Array UInt64 := #[entryAddr]
  while !queue.isEmpty do
    let cur := queue.back!
    queue := queue.pop
    if reachable.contains cur then pure ()
    else
      reachable := reachable.insert cur
      for (src, tgt) in callGraph do
        if src == cur && !reachable.contains tgt then
          queue := queue.push tgt
  return reachable

/-- Given an entry address, compute the transitive closure of the call graph
    and return only the functions reachable from that entry.
    Uses buildCallGraph (syntactic, no fixpoint needed). -/
def scopeByEntry (functions : Array FunctionSpec) (entryAddr : UInt64)
    (log : String → IO Unit) : IO (Array FunctionSpec) := do
  let callGraph ← buildCallGraph functions log
  let reachable := callGraphReachable entryAddr callGraph
  let result := functions.filter fun f => reachable.contains f.entryAddr
  log s!"\n=== Entry-point scoping from {hexAddr entryAddr} ==="
  log s!"  {result.size}/{functions.size} functions reachable"
  for f in result do
    log s!"    {f.name} @ {hexAddr f.entryAddr}"
  return result

/-- Resolve an entry point: by hex address or by function name. -/
def resolveEntry (functions : Array FunctionSpec) (entry : String) : Option UInt64 :=
  -- Try as hex address first
  match parseHexAddr entry with
  | some addr => if functions.any (·.entryAddr == addr) then some addr else none
  | none =>
    -- Try as function name
    match functions.find? (·.name == entry) with
    | some f => some f.entryAddr
    | none => none

/-! ## CLI Argument Parsing -/

/-- Parsed CLI configuration. -/
structure CLIConfig where
  jsonPath : Option System.FilePath := none
  elfBinary : Option System.FilePath := none
  jsonOutput : Bool := false
  functionsSpec : Option String := none  -- comma-separated names or addrs
  entry : Option String := none
  logPath : System.FilePath := ".lake/stabilization.log"
  showHelp : Bool := false
  diagnostics : Bool := false
  maxIter : Nat := 200
  maxBranches : Nat := 10000
  legacy : Bool := false  -- use old stratifiedFixpoint instead of WTO
  deriving Inhabited

/-- Parse comma-separated hex addresses. -/
private def parseAddrList (s : String) : Option (Array UInt64) :=
  let parts := s.splitOn ","
  let parsed := parts.filterMap fun p => parseHexAddr p.trimAscii.toString
  if parsed.length == parts.length then some parsed.toArray else none

/-- Resolve a comma-separated list of function names or addresses to FunctionSpecs.
    Returns the subset of functions matching the given names/addresses. -/
def resolveFunctionList (functions : Array FunctionSpec) (spec : String) : Array FunctionSpec :=
  let parts := spec.splitOn ","
  let names := parts.map (·.trimAscii.toString)
  functions.filter fun f =>
    names.any fun n =>
      f.name == n || (match parseHexAddr n with | some a => f.entryAddr == a | none => false)

/-- Parse CLI arguments into a CLIConfig. -/
private def parseCLIArgs : List String → CLIConfig → CLIConfig
  | [], cfg => cfg
  | "--help" :: rest, cfg => parseCLIArgs rest { cfg with showHelp := true }
  | "-h" :: rest, cfg => parseCLIArgs rest { cfg with showHelp := true }
  | "--json" :: rest, cfg => parseCLIArgs rest { cfg with jsonOutput := true }
  | "--diagnostics" :: rest, cfg => parseCLIArgs rest { cfg with diagnostics := true }
  | "--legacy" :: rest, cfg => parseCLIArgs rest { cfg with legacy := true }
  | "--functions" :: spec :: rest, cfg =>
    parseCLIArgs rest { cfg with functionsSpec := some spec }
  | "--entry" :: name :: rest, cfg => parseCLIArgs rest { cfg with entry := some name }
  | "--log" :: path :: rest, cfg => parseCLIArgs rest { cfg with logPath := path }
  | "--max-iter" :: n :: rest, cfg =>
    parseCLIArgs rest { cfg with maxIter := n.toNat! }
  | "--max-branches" :: n :: rest, cfg =>
    parseCLIArgs rest { cfg with maxBranches := n.toNat! }
  | arg :: rest, cfg =>
    if arg.startsWith "--" then
      parseCLIArgs rest cfg  -- skip unknown flags
    else if cfg.jsonPath.isNone then
      parseCLIArgs rest { cfg with jsonPath := some arg }
    else if cfg.elfBinary.isNone then
      parseCLIArgs rest { cfg with elfBinary := some arg }
    else
      parseCLIArgs rest cfg  -- extra positional args ignored

/-- Print usage/help text. -/
private def printUsage : IO Unit := do
  IO.eprintln "Usage: dispatchLoopEval [OPTIONS] <input.json> [elf-binary]"
  IO.eprintln "       dispatchLoopEval --test [--subject NAME]"
  IO.eprintln ""
  IO.eprintln "Extract grammars from binary dispatch loops via symbolic execution."
  IO.eprintln ""
  IO.eprintln "Arguments:"
  IO.eprintln "  <input.json>         Per-function blocks JSON (VEX IR)"
  IO.eprintln "  [elf-binary]         ELF binary for symbol-based function discovery"
  IO.eprintln ""
  IO.eprintln "Options:"
  IO.eprintln "  --json               Output results as structured JSON to stdout"
  IO.eprintln "  --entry NAME|ADDR    Scope to functions reachable from entry point"
  IO.eprintln "  --functions ADDRS    Comma-separated hex entry addresses to analyze"
  IO.eprintln "  --log PATH           Log file path (default: .lake/stabilization.log)"
  IO.eprintln "  --diagnostics        Run h_contains, closedness, template, atom-closed checks"
  IO.eprintln "  --max-iter N         Maximum composition iterations (default: 200)"
  IO.eprintln "  --max-branches N     Branch count cap before early stop (default: 10000)"
  IO.eprintln "  --legacy             Use legacy 2-phase stratifiedFixpoint instead of WTO"
  IO.eprintln "  --test               Run test suite (via dispatchLoopTest)"
  IO.eprintln "  --subject NAME       Run specific test subject (with --test)"
  IO.eprintln "  --help, -h           Show this help message"
  IO.eprintln ""
  IO.eprintln "Examples:"
  IO.eprintln "  dispatchLoopEval reference/tinyc/blocks.json --entry statement"
  IO.eprintln "  dispatchLoopEval reference/tinyc/blocks.json --entry 0x400678 --json"
  IO.eprintln "  dispatchLoopEval blocks.json tiny.o --functions 0x401234,0x401567"
  IO.eprintln "  dispatchLoopEval --test"

/-- Main entry point for dispatch loop evaluation with CLI args. -/
def dispatchLoopEvalMain (args : List String := []) : IO Unit := do
  let cfg := parseCLIArgs args {}
  if cfg.showHelp then
    printUsage
    return
  match cfg.jsonPath with
  | none =>
    printUsage
    IO.Process.exit 1
  | some jsonPath =>
    let log ← if cfg.jsonOutput
              then mkFileLogger cfg.logPath
              else mkLogger cfg.logPath
    match cfg.elfBinary with
    | some elfBinary =>
      -- File-based mode: blocks.json + ELF binary
      log s!"Loading blocks from {jsonPath}..."
      let blocks ← loadBlocksFromJSON jsonPath
      log s!"  {blocks.size} blocks loaded"
      log s!"Reading symbols from {elfBinary}..."
      let symbols ← ElfSymbolTable.readSymbolsFromFile elfBinary
      log s!"  {symbols.size} function symbols found"
      for (name, addr, size) in symbols do
        log s!"    {name} @ 0x{String.ofList (Nat.toDigits 16 addr.toNat)}, {size} bytes"
      match discoverFunctions blocks symbols with
      | .error e =>
        IO.eprintln s!"Function discovery error: {e}"
        IO.Process.exit 1
      | .ok result =>
        log s!"Discovered {result.functions.size} functions with blocks:"
        for f in result.functions do
          log s!"  {f.name}: {f.blocks.length} blocks"
        if result.orphanCount > 0 then
          log s!"  WARNING: {result.orphanCount} blocks not in any function symbol range"
        -- Scope functions: --entry then --functions
        let functions ← match cfg.entry with
          | some entry =>
            match resolveEntry result.functions entry with
            | some addr => scopeByEntry result.functions addr log
            | none =>
              IO.eprintln s!"Unknown entry point: {entry}"
              IO.Process.exit 1
          | none => pure result.functions
        let functions := match cfg.functionsSpec with
          | some spec => resolveFunctionList functions spec
          | none => functions
        let resolvedEntry := cfg.entry.bind (resolveEntry functions)
        if cfg.legacy then
          if cfg.jsonOutput then
            runPipelineJSON functions (log := log) (maxBranches := cfg.maxBranches) (diagnostics := cfg.diagnostics) (maxIter := cfg.maxIter)
          else
            runPipeline functions (log := log) (maxBranches := cfg.maxBranches) (diagnostics := cfg.diagnostics) (maxIter := cfg.maxIter)
        else
          if cfg.jsonOutput then
            runPipelineWTOJSON functions (log := log) (maxBranches := cfg.maxBranches) (diagnostics := cfg.diagnostics) (maxIter := cfg.maxIter) (entryAddr := resolvedEntry)
          else
            runPipelineWTO functions (log := log) (maxBranches := cfg.maxBranches) (diagnostics := cfg.diagnostics) (maxIter := cfg.maxIter) (entryAddr := resolvedEntry) (inputPath := cfg.jsonPath)
    | none =>
      -- Single JSON: per-function format
      log s!"Loading functions from {jsonPath}..."
      let (allFunctions, regions) ← loadFunctionsFromJSON jsonPath
      log s!"  {allFunctions.size} functions loaded, {regions.size} memory regions"
      for r in regions do
        log s!"    {r.name}: [0x{String.ofList (Nat.toDigits 16 r.vaddr.toNat)}, +{r.size}) {r.flags}"
      -- Scope functions: --entry (call graph reachability) then --functions (exact set)
      let functions ← match cfg.entry with
        | some entry =>
          match resolveEntry allFunctions entry with
          | some addr => scopeByEntry allFunctions addr log
          | none =>
            IO.eprintln s!"Unknown entry point: {entry}"
            IO.eprintln s!"Available: {", ".intercalate (allFunctions.map (·.name)).toList}"
            IO.Process.exit 1
        | none => pure allFunctions
      let functions := match cfg.functionsSpec with
        | some spec =>
          let filtered := resolveFunctionList functions spec
          filtered
        | none => functions
      let resolvedEntry := cfg.entry.bind (resolveEntry functions)
      if cfg.legacy then
        if cfg.jsonOutput then
          runPipelineJSON functions regions log (maxBranches := cfg.maxBranches) (diagnostics := cfg.diagnostics) (maxIter := cfg.maxIter)
        else
          runPipeline functions regions log (maxBranches := cfg.maxBranches) (diagnostics := cfg.diagnostics) (maxIter := cfg.maxIter)
      else
        if cfg.jsonOutput then
          runPipelineWTOJSON functions regions log (maxBranches := cfg.maxBranches) (diagnostics := cfg.diagnostics) (maxIter := cfg.maxIter) (entryAddr := resolvedEntry)
        else
          runPipelineWTO functions regions log (maxBranches := cfg.maxBranches) (diagnostics := cfg.diagnostics) (maxIter := cfg.maxIter) (entryAddr := resolvedEntry) (inputPath := cfg.jsonPath)
