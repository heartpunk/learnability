import Instances.ISAs.DispatchLoopFunctionStab

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA VexIRParser

/-! ## Path History — ordered composition event tracking

Branches carry an append-only path history alongside the flat PC. The flat
`pc` field remains for all existing uses (dedup, simplification, SMT, hashing).
The `history` field preserves the sequential ordering of composition events
for grammar extraction: which guards were encountered, which functions were
called/returned, and in what order.

PathHistory is a cons-list (persistent/immutable). Branches sharing a common
prefix (same body branch composed with different frontier branches) share the
prefix in memory. Cost per branch: O(composition depth) extra pointers. -/

/-- A path event: what happened at a composition step. -/
inductive PathEvent (Reg : Type) where
  | guard : SymPC Reg → PathEvent Reg       -- a PC guard encountered
  | call : UInt64 → PathEvent Reg           -- called function at this address
  | ret : UInt64 → PathEvent Reg            -- returned from function
  | entry : UInt64 → PathEvent Reg          -- entered this function

/-- Persistent path history — cons-list for prefix sharing. -/
inductive PathHistory (Reg : Type) where
  | root : PathHistory Reg
  | cons : PathEvent Reg → PathHistory Reg → PathHistory Reg

/-- Convert path history to array (most recent event first). -/
def PathHistory.toArray {Reg : Type} : PathHistory Reg → Array (PathEvent Reg)
  | .root => #[]
  | .cons e h => #[e] ++ h.toArray

/-- Length of path history. -/
def PathHistory.length {Reg : Type} : PathHistory Reg → Nat
  | .root => 0
  | .cons _ h => 1 + h.length

/-- Append a guard event to the history. -/
def PathHistory.guard {Reg : Type} (pc : SymPC Reg) (h : PathHistory Reg) : PathHistory Reg :=
  .cons (.guard pc) h

/-- Append a call event to the history. -/
def PathHistory.call {Reg : Type} (target : UInt64) (h : PathHistory Reg) : PathHistory Reg :=
  .cons (.call target) h

/-- Append a return event to the history. -/
def PathHistory.ret {Reg : Type} (target : UInt64) (h : PathHistory Reg) : PathHistory Reg :=
  .cons (.ret target) h

/-- Append an entry event to the history. -/
def PathHistory.entry {Reg : Type} (addr : UInt64) (h : PathHistory Reg) : PathHistory Reg :=
  .cons (.entry addr) h

/-- Split body branches into non-call (kept in body) and call-expanded
    (seeded into initial frontier), with path history tracking.

    Like `splitBodyAndExpandCalls` but records `.call target` and `.ret target`
    events on each call-expanded branch, preserving the sequential call order
    for grammar extraction. -/
def splitBodyAndExpandCallsH {Reg : Type} [DecidableEq Reg] [Fintype Reg] [BEq Reg]
    (ip_reg : Reg)
    (bodyArr : Array (Branch (SymSub Reg) (SymPC Reg)))
    (summaries : Std.HashMap UInt64 (Array (Branch (SymSub Reg) (SymPC Reg)))) :
    (Array (Branch (SymSub Reg) (SymPC Reg))  -- nonCallBody
    × Array (Branch (SymSub Reg) (SymPC Reg) × PathHistory Reg)  -- callResults with history
    × Nat × Nat × Nat) := Id.run do  -- callsExpanded, branchesAdded, dropped
  let isa := vexSummaryISA Reg
  let mut nonCallBody : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]
  let mut callResults : Array (Branch (SymSub Reg) (SymPC Reg) × PathHistory Reg) := #[]
  let mut callsExpanded : Nat := 0
  let mut branchesAdded : Nat := 0
  let mut dropped : Nat := 0
  for b in bodyArr do
    match extractRipTarget ip_reg b.sub with
    | some target =>
      match summaries.get? target with
      | some summaryBranches =>
        callsExpanded := callsExpanded + 1
        for sb in summaryBranches do
          let composed := b.compose isa sb
          match simplifyBranch composed with
          | none => dropped := dropped + 1
          | some b' =>
            -- Record call → guard → ret in history (most recent first in cons-list)
            let hist := PathHistory.root
              |>.call target
              |>.guard (isa.pc_lift b.sub sb.pc)
              |>.ret target
            callResults := callResults.push (b', hist)
            branchesAdded := branchesAdded + 1
      | none =>
        nonCallBody := nonCallBody.push b
    | none =>
      nonCallBody := nonCallBody.push b
  return (nonCallBody, callResults, callsExpanded, branchesAdded, dropped)


def stratifiedFixpoint
    (functions : Array FunctionSpec)
    (regions : Array MemRegion := #[])
    (log : String → IO Unit)
    (maxBranches : Nat := 10000)
    (diagnostics : Bool := false)
    (maxIter : Nat := 200) :
    IO (Std.HashMap UInt64 (Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)))) := do
  let ip_reg := Amd64Reg.rip
  -- Build address classifier from ELF memory regions.
  -- rsp and rbp are stack registers — addresses relative to them are in the
  -- stack region, which doesn't overlap any loaded ELF section.
  let addrClassify : Option (AddrClassifier Amd64Reg) :=
    if regions.size > 0 then
      some (classifyAddr regions [Amd64Reg.rsp, Amd64Reg.rbp])
    else none
  -- Parse all function blocks into raw body arrays
  let mut funcBlocks : Array (String × Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg))) := #[]
  for func in functions do
    let t_parse ← IO.monoMsNow
    match parseBlocksWithAddresses func.blocks with
    | .error e =>
      log s!"  PARSE ERROR for {func.name}: {e}"
      funcBlocks := funcBlocks.push (func.name, #[])
    | .ok pairs =>
      let t_parsed ← IO.monoMsNow
      let bodyArr := flatBodyDenotArray ip_reg pairs
      let t_body ← IO.monoMsNow
      funcBlocks := funcBlocks.push (func.name, bodyArr)
      log s!"  {func.name} @ 0x{String.ofList (Nat.toDigits 16 func.entryAddr.toNat)}: {pairs.length} blocks, {bodyArr.size} body branches ({t_parsed - t_parse}ms parse, {t_body - t_parsed}ms body)"
  -- Phase 1: Compute leaf function (next_sym) fixpoint — no summaries needed
  let mut summaries : Std.HashMap UInt64 (Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg))) := {}
  -- Green-style SMT query cache: shared across all function stabilizations
  let smtCache ← IO.mkRef ({} : SMTCache Amd64Reg)
  log s!"\n--- Phase 1: Leaf function (next_sym) ---"
  let t0 ← IO.monoMsNow
  let (nextSymName, nextSymBody) := funcBlocks[0]!
  -- Use computeFunctionStabilization directly (returns branch array as summary).
  -- Don't double-run with computeStabilizationHS — that keeps two copies of deeply-nested
  -- symbolic branches alive simultaneously, causing OOM.
  match ← computeFunctionStabilization ip_reg nextSymBody {} maxIter log smtCache (addrClassify := addrClassify) (maxBranches := maxBranches) (diagnostics := diagnostics) with
  | some (k, summaryArr) =>
    let t1 ← IO.monoMsNow
    summaries := summaries.insert functions[0]!.entryAddr summaryArr
    log s!"  {nextSymName}: converged at K={k}, {summaryArr.size} summary branches, {t1 - t0}ms"
  | none =>
    log s!"  {nextSymName}: DID NOT CONVERGE"
    return {}
  -- Phase 2: Iterate NT function summaries to fixpoint
  -- At each outer round, for each NT function:
  --   1. Split body into non-call blocks + call-expanded results (via splitBodyAndExpandCalls)
  --   2. Run stabilization on non-call body, seeding call results as initial frontier
  --   3. The converged set = new function summary
  -- Key: non-call body never contains summary-expanded branches, preventing expression nesting
  log s!"\n--- Phase 2: NT functions (mutual recursion) ---"
  -- Initialize NT summaries as empty
  for i in [1:functions.size] do
    summaries := summaries.insert functions[i]!.entryAddr #[]
  let mut outerRound : Nat := 0
  let mut outerChanged := true
  while outerChanged do
    outerChanged := false
    outerRound := outerRound + 1
    log s!"\n  === Outer round {outerRound} ==="
    for i in [1:functions.size] do
      let func := functions[i]!
      let (fname, rawBody) := funcBlocks[i]!
      let t0 ← IO.monoMsNow
      -- Step 1: Split body into non-call blocks + call-expanded results
      let (nonCallBody, callResults, callsExp, branchesAdded, droppedExp) :=
        splitBodyAndExpandCalls ip_reg rawBody summaries
      log s!"    {fname}: split body {rawBody.size} → {nonCallBody.size} non-call + {callResults.size} call-expanded ({callsExp} calls, {branchesAdded} branches, {droppedExp} dropped)"
      -- Step 2: Run stabilization on non-call body, seeding call results as initial frontier
      let oldSummary := summaries.getD func.entryAddr #[]
      match ← computeFunctionStabilization ip_reg nonCallBody {} (min maxIter 30) log smtCache (initialFrontier := callResults) (addrClassify := addrClassify) (maxBranches := maxBranches) (diagnostics := diagnostics) with
      | some (k, newSummary) =>
        let t1 ← IO.monoMsNow
        if newSummary.size != oldSummary.size then
          outerChanged := true
          summaries := summaries.insert func.entryAddr newSummary
          log s!"  {fname}: K={k}, {newSummary.size} branches (was {oldSummary.size}), {t1 - t0}ms [CHANGED]"
        else
          log s!"  {fname}: K={k}, {newSummary.size} branches (stable), {t1 - t0}ms"
      | none =>
        log s!"  {fname}: DID NOT CONVERGE"
        return {}
  log s!"\n=== Stratified fixpoint complete after {outerRound} outer rounds ==="
  for i in [:functions.size] do
    let func := functions[i]!
    let summary := summaries.getD func.entryAddr #[]
    log s!"  {func.name}: {summary.size} branches"
  -- SMT cache summary
  let cacheContents ← smtCache.get
  log s!"\n=== SMT Cache Summary ==="
  log s!"  cache entries: {cacheContents.size}"
  return summaries

/-! ## Weak Topological Ordering (Bourdoncle's Algorithm)

Bourdoncle's hierarchical decomposition ("Efficient Chaotic Iteration
Strategies with Widenings", 1993) computes the optimal iteration structure
for fixpoint computation over a call graph.

- Trivial SCCs (single vertex, no self-loop) → `WTOElem.vertex`
- Non-trivial SCCs → select head (first DFS-visited), recursively compute
  WTO of the SCC body, wrap in `WTOElem.component head body`

The recursive iteration strategy (Theorem 5): only check the **head** of each
component for stabilization — if the head hasn't changed, the whole component
is stable. For nested mutual recursion, inner loops converge before outer
loops re-iterate. -/

/-- A WTO element: either a single vertex or a component (head + body). -/
inductive WTOElem where
  | vertex : UInt64 → WTOElem
  | component : UInt64 → Array WTOElem → WTOElem
  deriving Inhabited

/-- Get the head address of a WTO element. -/
def WTOElem.head : WTOElem → UInt64
  | .vertex addr => addr
  | .component addr _ => addr

/-- DFS frame for iterative Tarjan: (node, successor_index, min_dfn). -/
structure TarjanFrame where
  node : UInt64
  succIdx : Nat
  minDfn : Nat
  deriving Inhabited

/-- Bourdoncle's WTO via modified Tarjan's SCC algorithm.
    Returns the WTO as an array of elements in topological order.
    Fuel bounds recursion depth (≤ number of nodes); never exhausted in practice. -/
def computeWTO (nodes : Array UInt64) (edges : Array (UInt64 × UInt64))
    (root : UInt64) (fuel : Nat := nodes.size + 1) : Array WTOElem :=
  match fuel with
  | 0 => #[]
  | fuel + 1 => Id.run do
  -- Adjacency list
  let mut adj : Std.HashMap UInt64 (Array UInt64) := {}
  for (src, tgt) in edges do
    adj := adj.insert src ((adj.getD src #[]).push tgt)
  -- DFS state
  let mut dfn : Std.HashMap UInt64 Nat := {}
  let mut num : Nat := 0
  let mut stack : Array UInt64 := #[]
  let mut onStack : Std.HashSet UInt64 := {}
  let mut result : Array WTOElem := #[]
  -- The node set for quick membership checks
  let nodeSet : Std.HashSet UInt64 := nodes.foldl (fun s n => s.insert n) {}
  let mut workStack : Array TarjanFrame := #[]
  -- Process starting from root, then any unreachable nodes
  let mut toVisit : Array UInt64 := #[root]
  for n in nodes do
    unless n == root do toVisit := toVisit.push n
  for startNode in toVisit do
    if dfn.contains startNode then continue
    -- Push initial frame
    num := num + 1
    dfn := dfn.insert startNode num
    stack := stack.push startNode
    onStack := onStack.insert startNode
    workStack := workStack.push ⟨startNode, 0, num⟩
    while !workStack.isEmpty do
      let frame := workStack.back!
      let succs := adj.getD frame.node #[]
      if frame.succIdx < succs.size then
        let succ := succs[frame.succIdx]!
        -- Advance successor index
        workStack := workStack.pop.push { frame with succIdx := frame.succIdx + 1 }
        if !nodeSet.contains succ then
          continue  -- skip edges to nodes outside our scope
        if !dfn.contains succ then
          -- Tree edge: visit successor
          num := num + 1
          dfn := dfn.insert succ num
          stack := stack.push succ
          onStack := onStack.insert succ
          workStack := workStack.push ⟨succ, 0, num⟩
        else if onStack.contains succ then
          -- Back edge: update min
          let succDfn := dfn.getD succ 0
          let curFrame := workStack.back!
          if succDfn < curFrame.minDfn then
            workStack := workStack.pop.push { curFrame with minDfn := succDfn }
      else
        -- All successors processed
        workStack := workStack.pop
        let nodeDfn := dfn.getD frame.node 0
        if frame.minDfn == nodeDfn then
          -- SCC head: pop the component from stack
          let mut component : Array UInt64 := #[]
          while !stack.isEmpty do
            let top := stack.back!
            stack := stack.pop
            onStack := onStack.erase top
            component := component.push top
            if top == frame.node then break
          if component.size == 1 then
            -- Check for self-loop
            let hasSelfLoop := (adj.getD frame.node #[]).any (· == frame.node)
            if hasSelfLoop then
              result := result.push (.component frame.node #[])
            else
              result := result.push (.vertex frame.node)
          else
            -- Non-trivial SCC: head is frame.node, rest are body
            -- Recursively compute WTO of the body members
            let bodyNodes := component.filter (· != frame.node)
            let bodyEdges := edges.filter fun (s, t) =>
              bodyNodes.any (· == s) && (bodyNodes.any (· == t) || t == frame.node)
            let bodyWTO := computeWTO bodyNodes bodyEdges frame.node fuel
            result := result.push (.component frame.node bodyWTO)
        else
          -- Propagate min to parent
          if !workStack.isEmpty then
            let parent := workStack.back!
            if frame.minDfn < parent.minDfn then
              workStack := workStack.pop.push { parent with minDfn := frame.minDfn }
  return result
termination_by fuel

/-- Pretty-print a WTO for logging. -/
partial def ppWTO (elems : Array WTOElem)
    (nameOf : UInt64 → String := fun a => s!"0x{String.ofList (Nat.toDigits 16 a.toNat)}") :
    String :=
  let rec ppElem : WTOElem → String
    | .vertex addr => nameOf addr
    | .component head body =>
      let bodyStr := ", ".intercalate (body.toList.map ppElem)
      s!"({nameOf head} {bodyStr})"
  " ".intercalate (elems.toList.map ppElem)

/-! ## WTO-based Fixpoint

Replaces the hardcoded 2-phase `stratifiedFixpoint` with a generic N-phase
structure driven by the WTO of the call graph. The convergence theorem
doesn't care about lexer/NT classification — it just needs summaries
available when composing.

Implements Bourdoncle's recursive iteration strategy:
- `vertex f` → analyze f once with current summaries
- `component head body` → repeat { analyze head; interpretWTO body }
  until head's summary stabilizes -/

/-- Flatten a WTO into a work-list for iterative interpretation.
    Each entry: (addr, isComponentHead, componentBodyElems).
    Component heads get `some body`; vertices get `none`. -/
def flattenWTOWork : Array WTOElem → Array (UInt64 × Option (Array WTOElem))
  | elems => elems.foldl (fun acc e => match e with
    | .vertex addr => acc.push (addr, none)
    | .component head body => acc.push (head, some body)) #[]

/-- WTO-driven fixpoint: analyze functions in weak topological order.
    For each vertex, analyze once. For each component, iterate until
    the head's summary stabilizes. -/
def wtoFixpoint
    (functions : Array FunctionSpec)
    (wto : Array WTOElem)
    (regions : Array MemRegion := #[])
    (log : String → IO Unit)
    (maxIter : Nat := 200)
    (maxBranches : Nat := 10000)
    (diagnostics : Bool := false)
    : IO (Std.HashMap UInt64 (Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)))) := do
  let ip_reg := Amd64Reg.rip
  let addrClassify : Option (AddrClassifier Amd64Reg) :=
    if regions.size > 0 then
      some (classifyAddr regions [Amd64Reg.rsp, Amd64Reg.rbp])
    else none
  -- Parse all function blocks into raw body arrays
  let mut funcBlocks : Std.HashMap UInt64 (String × Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg))) := {}
  for func in functions do
    let t_parse ← IO.monoMsNow
    match parseBlocksWithAddresses func.blocks with
    | .error e =>
      log s!"  PARSE ERROR for {func.name}: {e}"
      funcBlocks := funcBlocks.insert func.entryAddr (func.name, #[])
    | .ok pairs =>
      let t_parsed ← IO.monoMsNow
      let bodyArr := flatBodyDenotArray ip_reg pairs
      let t_body ← IO.monoMsNow
      funcBlocks := funcBlocks.insert func.entryAddr (func.name, bodyArr)
      log s!"  {func.name} @ 0x{String.ofList (Nat.toDigits 16 func.entryAddr.toNat)}: {pairs.length} blocks, {bodyArr.size} body branches ({t_parsed - t_parse}ms parse, {t_body - t_parsed}ms body)"
      log s!"  {func.name} @ 0x{String.ofList (Nat.toDigits 16 func.entryAddr.toNat)}: {pairs.length} blocks, {bodyArr.size} body branches"
  -- Initialize all summaries as empty
  let mut summaries : Std.HashMap UInt64 (Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg))) := {}
  for func in functions do
    summaries := summaries.insert func.entryAddr #[]
  -- Shared SMT cache
  let smtCache ← IO.mkRef ({} : SMTCache Amd64Reg)
  -- Name lookup for logging
  let nameOf (addr : UInt64) : String :=
    match functions.find? (·.entryAddr == addr) with
    | some f => f.name
    | none => s!"0x{String.ofList (Nat.toDigits 16 addr.toNat)}"
  log s!"\n=== WTO Fixpoint ==="
  log s!"  WTO: {ppWTO wto nameOf}"
  -- Process top-level WTO elements
  for elem in wto do
    match elem with
    | .vertex addr =>
      log s!"\n  --- vertex: {nameOf addr} ---"
      match funcBlocks.get? addr with
      | none => pure ()
      | some (fname, rawBody) =>
        let t0 ← IO.monoMsNow
        let (nonCallBody, callResults, callsExp, branchesAdded, droppedExp) :=
          splitBodyAndExpandCalls ip_reg rawBody summaries
        log s!"    {fname}: split {rawBody.size} → {nonCallBody.size} non-call + {callResults.size} call-expanded ({callsExp} calls, +{branchesAdded}, -{droppedExp})"
        match ← computeFunctionStabilization ip_reg nonCallBody {} maxIter log smtCache
            (initialFrontier := callResults) (addrClassify := addrClassify)
            (maxBranches := maxBranches) (diagnostics := diagnostics) with
        | some (k, summaryArr) =>
          let t1 ← IO.monoMsNow
          log s!"    {fname}: converged K={k}, {summaryArr.size} branches, {t1 - t0}ms"
          summaries := summaries.insert addr summaryArr
        | none =>
          log s!"    {fname}: DID NOT CONVERGE"
    | .component head body =>
      log s!"\n  === component head: {nameOf head} ==="
      -- Bourdoncle's recursive strategy: iterate {head; body} until head stabilizes
      -- For nested components in body, we flatten: analyze each body element once per round
      let bodyWork := flattenWTOWork body
      let mut round : Nat := 0
      let mut stable := false
      while !stable && round < maxIter do
        round := round + 1
        log s!"\n  --- component round {round}, head: {nameOf head} ---"
        let oldSize := (summaries.getD head #[]).size
        -- Analyze head
        match funcBlocks.get? head with
        | none => stable := true
        | some (fname, rawBody) =>
          let t0 ← IO.monoMsNow
          let (nonCallBody, callResults, callsExp, branchesAdded, droppedExp) :=
            splitBodyAndExpandCalls ip_reg rawBody summaries
          log s!"    {fname}: split {rawBody.size} → {nonCallBody.size} non-call + {callResults.size} call-expanded ({callsExp} calls, +{branchesAdded}, -{droppedExp})"
          match ← computeFunctionStabilization ip_reg nonCallBody {} maxIter log smtCache
              (initialFrontier := callResults) (addrClassify := addrClassify)
              (maxBranches := maxBranches) (diagnostics := diagnostics) with
          | some (k, summaryArr) =>
            let t1 ← IO.monoMsNow
            log s!"    {fname}: converged K={k}, {summaryArr.size} branches, {t1 - t0}ms"
            summaries := summaries.insert head summaryArr
          | none =>
            log s!"    {fname}: DID NOT CONVERGE"
            stable := true  -- bail on divergence
        -- Analyze body elements
        for (addr, nested) in bodyWork do
          match funcBlocks.get? addr with
          | none => pure ()
          | some (fname, rawBody) =>
            let t0 ← IO.monoMsNow
            let (nonCallBody, callResults, callsExp, branchesAdded, droppedExp) :=
              splitBodyAndExpandCalls ip_reg rawBody summaries
            log s!"    {fname}: split {rawBody.size} → {nonCallBody.size} non-call + {callResults.size} call-expanded ({callsExp} calls, +{branchesAdded}, -{droppedExp})"
            -- Nested component heads get iterated too
            let iterLimit := match nested with
              | some _ => maxIter  -- nested component head: may need iteration
              | none => maxIter
            match ← computeFunctionStabilization ip_reg nonCallBody {} iterLimit log smtCache
                (initialFrontier := callResults) (addrClassify := addrClassify)
                (maxBranches := maxBranches) (diagnostics := diagnostics) with
            | some (k, summaryArr) =>
              let t1 ← IO.monoMsNow
              log s!"    {fname}: converged K={k}, {summaryArr.size} branches, {t1 - t0}ms"
              summaries := summaries.insert addr summaryArr
            | none =>
              log s!"    {fname}: DID NOT CONVERGE"
        -- Check if head stabilized
        let newSize := (summaries.getD head #[]).size
        if newSize == oldSize then
          stable := true
          log s!"  component head {nameOf head} stable after {round} rounds"
  log s!"\n=== WTO Fixpoint complete ==="
  for func in functions do
    let summary := summaries.getD func.entryAddr #[]
    log s!"  {func.name}: {summary.size} branches"
  let cacheContents ← smtCache.get
  log s!"\n=== SMT Cache Summary ==="
  log s!"  cache entries: {cacheContents.size}"
  return summaries

