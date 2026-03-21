import Instances.ISAs.DispatchLoopSMT

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA VexIRParser

/-! ## Semantic Closedness Witness Finding

Given a set of branches and a closure, find for each (branch, guard) pair
a closure member that is semantically equivalent to the lifted guard.
This is the untrusted CVC5 oracle — witnesses are verified by bv_decide
at build time. CVC5 is NOT in the TCB. -/

/-- Evidence for how a lifted PC relates to the closure. -/
inductive SemClosedWitness where
  | trivialFalse                  -- lifted PC simplified to unsatisfiable
  | trivialTrue                   -- lifted PC simplified to tautology
  | witness (closureIdx : Nat)    -- closure[closureIdx] is semantically equivalent
  | noWitness                     -- no equivalent closure member found (violation)
  deriving Repr, Inhabited

/-- For each (branch, guard) pair, find a closure member semantically equivalent
    to the lifted guard `substSymPC b.sub φ`. Uses CVC5 as an untrusted oracle.

    Returns array of `(branch_idx, guard_idx, evidence)` triples covering all
    `branches.size × closure.size` pairs. The evidence records HOW closedness
    was established:
    - `trivialFalse` / `trivialTrue`: simplified to constant (bv_decide verifies)
    - `witness j`: `closure[j]` is semantically equivalent (bv_decide verifies)
    - `noWitness`: no equivalent found (closedness violation) -/
def findSemClosedWitnesses {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    [Hashable Reg] [BEq Reg] [ToString Reg]
    (branches : Array (Branch (SymSub Reg) (SymPC Reg)))
    (closure : Array (SymPC Reg))
    (smtCache : IO.Ref (SMTCache Reg))
    (log : String → IO Unit := fun _ => pure ()) :
    IO (Array (Nat × Nat × SemClosedWitness)) := do
  let mut results : Array (Nat × Nat × SemClosedWitness) := #[]
  -- Phase 1: Classify each pair (trivial / syntactic / needs SMT)
  -- smtPCs collects simplified PCs needing SMT; smtMeta tracks their (b_idx, phi_idx)
  let mut smtPCs : Array (SymPC Reg) := #[]
  let mut smtMeta : Array (Nat × Nat) := #[]
  let mut b_idx : Nat := 0
  for b in branches do
    let mut phi_idx : Nat := 0
    for phi in closure do
      let lifted := substSymPC b.sub phi
      let liftedSimplified := simplifyLoadStorePC lifted
      match SymPC.simplifyConst liftedSimplified with
      | none =>
        results := results.push (b_idx, phi_idx, .trivialFalse)
      | some .true =>
        results := results.push (b_idx, phi_idx, .trivialTrue)
      | some pc' =>
        -- Syntactic match against closure
        let mut found := false
        let mut j : Nat := 0
        for phi_j in closure do
          if !found && phi_j == pc' then
            results := results.push (b_idx, phi_idx, .witness j)
            found := true
          j := j + 1
        unless found do
          smtPCs := smtPCs.push pc'
          smtMeta := smtMeta.push (b_idx, phi_idx)
      phi_idx := phi_idx + 1
    b_idx := b_idx + 1
  log s!"  [witnesses] total={branches.size * closure.size} trivial+syntactic={results.size} smt_candidates={smtPCs.size}"
  -- Phase 2: Batch SMT equivalence check for remaining pairs.
  -- For each candidate, check against ALL closure members in one batch.
  -- Equivalence = forward implication + reverse implication.
  if smtPCs.size > 0 then
    let n := closure.size
    let mut allFwdPairs : Array (SymPC Reg × SymPC Reg) := #[]
    let mut allRevPairs : Array (SymPC Reg × SymPC Reg) := #[]
    for pc' in smtPCs do
      for phi_j in closure do
        allFwdPairs := allFwdPairs.push (pc', phi_j)
        allRevPairs := allRevPairs.push (phi_j, pc')
    let (fwdResults, fwdHits) ← smtCheckImplCached smtCache allFwdPairs ".lake/smt_witness.smt2"
    let (revResults, revHits) ← smtCheckImplCached smtCache allRevPairs ".lake/smt_witness.smt2"
    log s!"  [witnesses] smt: {allFwdPairs.size * 2} queries (cache hits={fwdHits + revHits})"
    -- Map results back: candidate i's closure comparisons are at [i*n .. (i+1)*n)
    let mut smtFound : Nat := 0
    for ci in [:smtPCs.size] do
      if h_ci : ci < smtMeta.size then
        let (bi, pi) := smtMeta[ci]
        let base := ci * n
        let mut witnessFound := false
        for j in [:n] do
          if !witnessFound then
            let idx := base + j
            if h1 : idx < fwdResults.size then
              if h2 : idx < revResults.size then
                if fwdResults[idx] && revResults[idx] then
                  results := results.push (bi, pi, .witness j)
                  witnessFound := true
                  smtFound := smtFound + 1
        unless witnessFound do
          results := results.push (bi, pi, .noWitness)
    let violations := smtPCs.size - smtFound
    log s!"  [witnesses] smt_found={smtFound} violations={violations}"
  return results

/-- Prefix all SMT variable names in an SMT-LIB string.
    Replaces `reg_` with `{prefix}reg_` and `base_mem` with `{prefix}base_mem`. -/
def prefixSMTVars (pfx : String) (smt : String) : String :=
  smt.replace "reg_" (pfx ++ "reg_") |>.replace "base_mem" (pfx ++ "base_mem")

/-- Check SemClosed per-pair using two-state CVC5 queries.
    For each lifted PC, checks: if two states agree on all closure PCs,
    do they agree on the lifted PC?

    Query: (closure agreement ∧ lifted disagreement) is UNSAT?
    UNSAT → SemClosed holds for this pair. -/
def smtCheckSemClosedBatch {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    [Hashable Reg] [BEq Reg] [ToString Reg]
    (liftedPCs : Array (SymPC Reg))
    (closure : Array (SymPC Reg))
    (log : String → IO Unit := fun _ => pure ())
    (tmpFile : System.FilePath := ".lake/smt_semclosed.smt2") :
    IO (Array Bool) := do
  if liftedPCs.size == 0 then return #[]
  -- Collect register names from ALL PCs (lifted + closure)
  let mut regNames : Std.HashSet String := {}
  let mut needsMem := false
  for pc in liftedPCs do
    regNames := SymPC.collectRegNames pc regNames
    if SymPC.hasLoad pc then needsMem := true
  for pc in closure do
    regNames := SymPC.collectRegNames pc regNames
    if SymPC.hasLoad pc then needsMem := true
  -- Build two-state preamble: s1_ and s2_ prefixed variables
  let mut preamble := "(set-logic QF_UFBV)\n"
  for name in regNames do
    preamble := preamble ++ s!"(declare-const s1_{name} (_ BitVec 64))\n"
    preamble := preamble ++ s!"(declare-const s2_{name} (_ BitVec 64))\n"
  if needsMem then
    preamble := preamble ++ "(declare-sort Mem 0)\n"
    preamble := preamble ++ "(declare-const s1_base_mem Mem)\n"
    preamble := preamble ++ "(declare-const s2_base_mem Mem)\n"
    for w in ["8", "16", "32", "64"] do
      preamble := preamble ++ s!"(declare-fun load_{w} (Mem (_ BitVec 64)) (_ BitVec 64))\n"
      preamble := preamble ++ s!"(declare-fun store_{w} (Mem (_ BitVec 64) (_ BitVec 64)) Mem)\n"
  -- Build closure agreement assertions (persistent across push/pop)
  let mut agreeAsserts := ""
  for psi in closure do
    let psiSMT := SymPC.toSMTLib psi
    let s1Psi := prefixSMTVars "s1_" psiSMT
    let s2Psi := prefixSMTVars "s2_" psiSMT
    agreeAsserts := agreeAsserts ++ s!"(assert (= {s1Psi} {s2Psi}))\n"
  -- Build incremental script: for each lifted PC, push/assert-disagree/check/pop
  let mut script := preamble ++ agreeAsserts
  for lifted in liftedPCs do
    let liftedSMT := SymPC.toSMTLib lifted
    let s1Lifted := prefixSMTVars "s1_" liftedSMT
    let s2Lifted := prefixSMTVars "s2_" liftedSMT
    script := script ++ "(push)\n"
    script := script ++ s!"(assert (not (= {s1Lifted} {s2Lifted})))\n"
    script := script ++ "(check-sat)\n"
    script := script ++ "(pop)\n"
  script := script ++ "(exit)\n"
  IO.FS.writeFile tmpFile script
  let smtOut ← IO.Process.output { cmd := "cvc5", args := #["--incremental", tmpFile.toString] }
  let results := parseSMTResults smtOut.stdout
  log s!"  [semclosed-smt] {liftedPCs.size} two-state queries, {results.filter id |>.size} pass"
  return results

/-! ## PC-Signature Equivalence Class Dedup

Two branches with the same substitution and the same PC signature (which guard PCs
from the closure they satisfy) will behave identically in all future compositions.
The convergence proof (`dispatch_branchClassesStable`) shows K ≤ 2^|closure| because
there are only that many distinct signature classes.

By deduplicating on (sub, signature), we collapse exponentially many branches into
at most 2^|closure| classes per distinct substitution, preventing the ~5x/iteration
blowup that causes OOM. -/

/-- Check if a guard PC is a rip-routing guard (eq (reg ip) (const addr)).
    These are determined by control flow path, not by data — filtering them
    out gives the data-only closure (P₀ from the convergence plan). -/
def isRipGuardPC {Reg : Type} [BEq Reg] (ip_reg : Reg) : SymPC Reg → Bool
  | .eq (.reg r) (.const _) => r == ip_reg
  | .eq (.const _) (.reg r) => r == ip_reg
  | _ => false

/-- Extract the closure from body branches: all distinct atomic conjuncts
    appearing in any body branch's PC.
    If `dataOnly` is true, filters out rip-routing guards (eq rip (const addr)),
    keeping only data-level guard PCs. This gives P₀ from the convergence plan. -/
def extractClosure {Reg : Type} [BEq Reg] [BEq (SymPC Reg)] [Hashable (SymPC Reg)]
    (ip_reg : Reg) (bodyArr : Array (Branch (SymSub Reg) (SymPC Reg)))
    (dataOnly : Bool := false) :
    Array (SymPC Reg) × Nat × Nat := Id.run do
  let mut seen : Std.HashSet (SymPC Reg) := {}
  let mut result : Array (SymPC Reg) := #[]
  let mut ripCount : Nat := 0
  let mut dataCount : Nat := 0
  for b in bodyArr do
    let conjuncts := SymPC.conjuncts b.pc
    for c in conjuncts do
      unless seen.contains c do
        seen := seen.insert c
        if isRipGuardPC ip_reg c then
          ripCount := ripCount + 1
          unless dataOnly do
            result := result.push c
        else
          dataCount := dataCount + 1
          result := result.push c
  return (result, ripCount, dataCount)

/-- Check h_contains: every branch's PC is determined by the closure.
    Verifies that all top-level conjuncts of each b.pc appear in the closure.
    This is the computational check for the abstract `h_contains` hypothesis
    (see `evalSymPC_of_conjunctsInClosure` in VexPipelineBridge.lean for soundness).
    Returns (allPassed, failureCount, ripMisses, dataMisses). -/
def checkHContains {Reg : Type} [DecidableEq Reg] [BEq Reg] [Hashable (SymPC Reg)]
    (ip_reg : Reg) (branches : Array (Branch (SymSub Reg) (SymPC Reg)))
    (closure : Array (SymPC Reg)) : Bool × Nat × Nat × Nat := Id.run do
  let closureSet : Std.HashSet (SymPC Reg) :=
    closure.foldl (fun s pc => s.insert pc) {}
  let mut ripMisses : Nat := 0
  let mut dataMisses : Nat := 0
  for b in branches do
    for c in SymPC.conjuncts b.pc do
      unless closureSet.contains c do
        if isRipGuardPC ip_reg c then
          ripMisses := ripMisses + 1
        else
          dataMisses := dataMisses + 1
  let total := ripMisses + dataMisses
  return (total == 0, total, ripMisses, dataMisses)

/-- Compute the PC signature of a branch w.r.t. a closure.
    Returns a list of bools: for each guard PC in the closure, does the branch's
    PC syntactically imply it?

    This is the computational analog of `pcSignatureWith` from VexDispatchLoop.lean,
    which filters the closure to the subset satisfied by a concrete state.
    Here we work purely syntactically: a branch's PC "satisfies" a guard PC if
    the branch's PC syntactically implies it (all conjuncts of the guard appear
    in the branch's conjuncts). -/
def computePCSignature {Reg : Type} [DecidableEq Reg] [Hashable Reg] [Hashable (SymPC Reg)]
    (closure : Array (SymPC Reg)) (pc : SymPC Reg)
    (closureCanon : Option (Array (SymPC Reg)) := none) : List Bool :=
  -- Canonicalize then extract conjuncts for O(1) membership checks.
  -- Canonicalization ensures that e.g. eq(a,b) and eq(b,a) hash identically,
  -- catching more syntactic matches before falling through to the SMT solver.
  let pcConjList := SymPC.conjuncts (canonicalizePC pc)
  let pcConjSet : Std.HashSet (SymPC Reg) :=
    pcConjList.foldl (fun s c => s.insert c) {}
  -- Use pre-canonicalized closure if provided (avoids re-canonicalizing
  -- the same closure PCs for every branch).
  let canon := closureCanon.getD (closure.map canonicalizePC)
  canon.toList.map fun cpc =>
    match cpc with
    | .true => true
    | _ => pcConjSet.contains cpc

/-- Hash a PC signature (list of bools) for use as a HashMap key. -/
def hashPCSignature (sig : List Bool) : UInt64 :=
  sig.foldl (fun acc b => mixHash acc (if b then 1 else 0)) 7

/-- Key for PC-signature dedup: combines substitution with PC signature.
    Two branches with the same dedup key are in the same equivalence class.
    Uses structural equality on `sub` (not hash) to avoid hash-collision unsoundness. -/
structure SigDedupKey (Reg : Type) [DecidableEq Reg] [Fintype Reg] where
  sub : SymSub Reg
  sig : List Bool

instance {Reg : Type} [DecidableEq Reg] [Fintype Reg] : BEq (SigDedupKey Reg) where
  beq k₁ k₂ := decide (k₁.sub = k₂.sub) && k₁.sig == k₂.sig

instance {Reg : Type} [DecidableEq Reg] [Fintype Reg] [Hashable Reg] [EnumReg Reg] :
    Hashable (SigDedupKey Reg) where
  hash k := mixHash (hash k.sub) (hashPCSignature k.sig)

/-- Dedup an array of branches by (sub, PC-signature) equivalence class.
    Returns (dedupedArray, collapsedCount). -/
def dedupBySignature {Reg : Type} [DecidableEq Reg] [Fintype Reg] [Hashable Reg] [EnumReg Reg]
    (closure : Array (SymPC Reg))
    (branches : Array (Branch (SymSub Reg) (SymPC Reg))) :
    Array (Branch (SymSub Reg) (SymPC Reg)) × Nat := Id.run do
  let mut seen : Std.HashSet (SigDedupKey Reg) := {}
  let mut result : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]
  let mut collapsed : Nat := 0
  for b in branches do
    let sig := computePCSignature closure b.pc
    let key : SigDedupKey Reg := ⟨b.sub, sig⟩
    if seen.contains key then
      collapsed := collapsed + 1
    else
      seen := seen.insert key
      result := result.push b
  return (result, collapsed)

/-! ## HashSet-based Stabilization (fast path)

Uses `Std.HashSet` for O(1) membership checks instead of Finset's O(n) linear scan.
The Hashable instances on SymExpr/SymPC/SymSub/Branch enable this. -/

/-- Extract the rip-guard address from a branch's PC.
    Body branches from `flatBodyDenot` have PCs of the form
    `and (eq (reg ip) (const addr)) rest` or just `eq (reg ip) (const addr)`.
    After stabilization rounds, the outermost rip guard is always the left
    conjunct (inner rip guards simplify to true/false via simplifyConst). -/
def extractRipGuard {Reg : Type} [BEq Reg] (ip_reg : Reg) :
    SymPC Reg → Option UInt64
  | .and (.eq (.reg r) (.const addr)) _ => if r == ip_reg then some addr else none
  | .and left _ => extractRipGuard ip_reg left  -- recurse into left-nested ands
  | .eq (.reg r) (.const addr) => if r == ip_reg then some addr else none
  | _ => none

/-- Extract the rip target from a body branch's substitution.
    If the branch maps ip_reg to a constant, that's the next block address. -/
def extractRipTarget {Reg : Type} (ip_reg : Reg) (sub : SymSub Reg) :
    Option UInt64 :=
  match sub.regs ip_reg with
  | .const addr => some addr
  | _ => none

/-- Compose body branches with frontier branches, simplify, return as Array.
    Uses direct iteration instead of Finset.biUnion/image.
    Returns (result, totalPairs, droppedCount). -/
def composeBranchArraySimplified {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (bodyArr frontierArr : Array (Branch (SymSub Reg) (SymPC Reg))) :
    Array (Branch (SymSub Reg) (SymPC Reg)) × Nat × Nat := Id.run do
  let isa := vexSummaryISA Reg
  let mut result : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]
  let mut dropped : Nat := 0
  for b1 in bodyArr do
    for b2 in frontierArr do
      let composed := b1.compose isa b2
      match simplifyBranch composed with
      | none => dropped := dropped + 1
      | some b' => result := result.push b'
  return (result, bodyArr.size * frontierArr.size, dropped)

/-- Rip-indexed composition: only compose body branches with frontier branches
    whose rip-guard matches the body branch's rip target.

    In the dispatch loop, `body.compose(frontier)` produces:
      pc = and body.pc (lift body.sub frontier.pc)
    The frontier's rip guard `eq (reg rip) (const addr)` gets lifted to
    `eq (body.sub.regs rip) (const addr)`. If body.sub.regs rip = const X,
    this is `eq (const X) (const addr)` — satisfiable iff X == addr.

    By indexing frontier branches by their rip-guard address and looking up
    body.sub.regs rip, we skip ~94% of compositions that would be dropped.

    Returns (result, totalPairs, skippedByIndex, droppedBySimplify). -/
def composeBranchArrayIndexed {Reg : Type} [DecidableEq Reg] [Fintype Reg] [BEq Reg]
    (ip_reg : Reg) (bodyArr frontierArr : Array (Branch (SymSub Reg) (SymPC Reg))) :
    Array (Branch (SymSub Reg) (SymPC Reg) × Nat) × Nat × Nat × Nat := Id.run do
  let isa := vexSummaryISA Reg
  -- Build frontier index: rip-guard addr → array of frontier branches
  let mut frontierByRip : Std.HashMap UInt64 (Array (Branch (SymSub Reg) (SymPC Reg))) := {}
  let mut frontierNoRip : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]
  for f in frontierArr do
    match extractRipGuard ip_reg f.pc with
    | some addr =>
      let arr := frontierByRip.getD addr #[]
      frontierByRip := frontierByRip.insert addr (arr.push f)
    | none => frontierNoRip := frontierNoRip.push f
  -- Compose using index, tracking which body branch produced each result
  let mut result : Array (Branch (SymSub Reg) (SymPC Reg) × Nat) := #[]
  let mut dropped : Nat := 0
  let mut composed_count : Nat := 0
  let totalPairs := bodyArr.size * frontierArr.size
  let mut bodyIdx : Nat := 0
  for b in bodyArr do
    -- Determine which frontier branches this body can reach
    let compatible := match extractRipTarget ip_reg b.sub with
      | some target => (frontierByRip.getD target #[]) ++ frontierNoRip
      | none => frontierArr  -- can't determine target, fall back to all
    for f in compatible do
      composed_count := composed_count + 1
      let composed := b.compose isa f
      match simplifyBranch composed with
      | none => dropped := dropped + 1
      | some b' => result := result.push (b', bodyIdx)
    bodyIdx := bodyIdx + 1
  let skipped := totalPairs - composed_count
  return (result, composed_count, skipped, dropped)

/-- Per-chunk composition result for parallel merge. -/
structure ChunkResult (Sub PC : Type*) where
  branches : Array (Branch Sub PC)
  composed : Nat
  dropped : Nat

/-- Compose a chunk of body branches with the frontier (rip-indexed).
    Pure function — no shared mutable state, safe to run in parallel. -/
def composeChunk {Reg : Type} [DecidableEq Reg] [Fintype Reg] [BEq Reg]
    (ip_reg : Reg) (bodyChunk : Array (Branch (SymSub Reg) (SymPC Reg)))
    (frontierByRip : Std.HashMap UInt64 (Array (Branch (SymSub Reg) (SymPC Reg))))
    (frontierNoRip : Array (Branch (SymSub Reg) (SymPC Reg)))
    (frontierAll : Array (Branch (SymSub Reg) (SymPC Reg))) :
    ChunkResult (SymSub Reg) (SymPC Reg) := Id.run do
  let isa := vexSummaryISA Reg
  let mut result : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]
  let mut dropped : Nat := 0
  let mut composed_count : Nat := 0
  for b in bodyChunk do
    let compatible := match extractRipTarget ip_reg b.sub with
      | some target => (frontierByRip.getD target #[]) ++ frontierNoRip
      | none => frontierAll
    for f in compatible do
      composed_count := composed_count + 1
      let composed := b.compose isa f
      match simplifyBranch composed with
      | none => dropped := dropped + 1
      | some b' => result := result.push b'
  return ⟨result, composed_count, dropped⟩

/-- Split an array into N roughly-equal chunks. -/
def splitIntoChunks {α : Type} (arr : Array α) (n : Nat) : Array (Array α) := Id.run do
  if n == 0 || arr.size == 0 then return #[arr]
  let chunkSize := (arr.size + n - 1) / n
  let mut chunks : Array (Array α) := #[]
  let mut i := 0
  while i < arr.size do
    let endIdx := min (i + chunkSize) arr.size
    chunks := chunks.push (arr.extract i endIdx)
    i := endIdx
  return chunks

/-- Parallel rip-indexed composition with dedup.
    Splits body array into chunks, composes each chunk in parallel via IO.asTask,
    then merges results into the HashSet sequentially.
    Returns (newBranches, updatedCurrent, pairsComposed, skipped, dropped, dupes). -/
def composeAndDedupParallel {Reg : Type} [DecidableEq Reg] [Fintype Reg] [Hashable Reg] [EnumReg Reg] [BEq Reg]
    (ip_reg : Reg) (bodyArr frontierArr : Array (Branch (SymSub Reg) (SymPC Reg)))
    (current : Std.HashSet (Branch (SymSub Reg) (SymPC Reg)))
    (numWorkers : Nat := 8) :
    IO (Array (Branch (SymSub Reg) (SymPC Reg)) × Std.HashSet (Branch (SymSub Reg) (SymPC Reg))
      × Nat × Nat × Nat × Nat) := do
  -- Build frontier index (shared across workers, immutable)
  let (frontierByRip, frontierNoRip) ← do
    let mut byRip : Std.HashMap UInt64 (Array (Branch (SymSub Reg) (SymPC Reg))) := {}
    let mut noRip : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]
    for f in frontierArr do
      match extractRipGuard ip_reg f.pc with
      | some addr =>
        let arr := byRip.getD addr #[]
        byRip := byRip.insert addr (arr.push f)
      | none => noRip := noRip.push f
    pure (byRip, noRip)
  -- Split body into chunks and spawn tasks
  let chunks := splitIntoChunks bodyArr numWorkers
  let tasks ← chunks.mapM fun chunk =>
    IO.asTask (prio := .dedicated) do
      return composeChunk ip_reg chunk frontierByRip frontierNoRip frontierArr
  -- Collect results
  let results ← tasks.mapM fun task => do
    let r ← IO.wait task
    IO.ofExcept r
  -- Merge into HashSet (sequential — avoids concurrent mutation)
  let mut newBranches : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]
  let mut cur := current
  let mut totalComposed : Nat := 0
  let mut totalDropped : Nat := 0
  let mut dupes : Nat := 0
  for r in results do
    totalComposed := totalComposed + r.composed
    totalDropped := totalDropped + r.dropped
    for b in r.branches do
      if cur.contains b then
        dupes := dupes + 1
      else
        newBranches := newBranches.push b
        cur := cur.insert b
  let totalPairs := bodyArr.size * frontierArr.size
  let skipped := totalPairs - totalComposed
  return (newBranches, cur, totalComposed, skipped, totalDropped, dupes)

/-! ## Template extraction and matching for anti-unification-based dedup

When the ground PC closure explodes, anti-unify consecutive-round PCs to
extract templates. PCs that are instances of a known template can be collapsed,
since they represent the same "shape" with different data values (holes). -/

/-- Pair PCs from previous and current frontier by body branch index.
    Groups both arrays by body index, then produces (old, new) pairs
    within each group. Only pairs PCs that share the same body index
    AND the same substitution hash (to avoid pairing unrelated paths). -/
def pairFrontierPCs {Reg : Type} [DecidableEq Reg] [Fintype Reg] [Hashable Reg] [EnumReg Reg]
    (previous current : Array (Branch (SymSub Reg) (SymPC Reg) × Nat))
    : Array (SymPC Reg × SymPC Reg) := Id.run do
  -- Build index: bodyIdx → array of PCs (with sub hash for filtering)
  let mut prevByBody : Std.HashMap Nat (Array (SymPC Reg × UInt64)) := {}
  for (b, bodyIdx) in previous do
    let arr := prevByBody.getD bodyIdx #[]
    prevByBody := prevByBody.insert bodyIdx (arr.push (b.pc, hash b.sub))
  let mut pairs : Array (SymPC Reg × SymPC Reg) := #[]
  for (b, bodyIdx) in current do
    let subH := hash b.sub
    if let some prevPCs := prevByBody.get? bodyIdx then
      for (prevPC, prevSubH) in prevPCs do
        -- Only pair PCs from branches with the same sub hash
        if prevSubH == subH && prevPC != b.pc then
          pairs := pairs.push (prevPC, b.pc)
  return pairs

/-- Extract templates from PC pairs via anti-unification.
    Filters trivial (0-hole) results — those are just identical PCs
    and don't help with dedup. -/
def extractTemplatesFromPairs {Reg : Type} [DecidableEq Reg]
    (pairs : Array (SymPC Reg × SymPC Reg))
    : Array (TemplatePC Reg) := Id.run do
  let mut templates : Array (TemplatePC Reg) := #[]
  for (l, r) in pairs do
    let (tpc, _) := VexISA.antiUnify l r
    if tpc.isParametric then
      templates := templates.push tpc
  return templates

mutual
/-- Match a template expression against a ground expression.
    Returns `some bindings` if the ground expression is an instance of the
    template, where `bindings` maps hole IDs to ground sub-expressions.
    Returns `none` on mismatch. -/
def matchTemplateExpr {Reg : Type} [DecidableEq Reg]
    (bindings : Std.HashMap HoleId (SymExpr Reg))
    (t : TemplateExpr Reg) (e : SymExpr Reg)
    : Option (Std.HashMap HoleId (SymExpr Reg)) :=
  match t with
  | .hole h =>
    match bindings.get? h with
    | some existing => if existing == e then some bindings else none
    | none => some (bindings.insert h e)
  | .const v => match e with | .const v' => if v == v' then some bindings else none | _ => none
  | .reg r => match e with | .reg r' => if r == r' then some bindings else none | _ => none
  | .low32 tx => match e with | .low32 ex => matchTemplateExpr bindings tx ex | _ => none
  | .uext32 tx => match e with | .uext32 ex => matchTemplateExpr bindings tx ex | _ => none
  | .sext8to32 tx => match e with | .sext8to32 ex => matchTemplateExpr bindings tx ex | _ => none
  | .sext32to64 tx => match e with | .sext32to64 ex => matchTemplateExpr bindings tx ex | _ => none
  | .sub32 ta tb => match e with
    | .sub32 ea eb => (matchTemplateExpr bindings ta ea).bind (matchTemplateExpr · tb eb)
    | _ => none
  | .shl32 ta tb => match e with
    | .shl32 ea eb => (matchTemplateExpr bindings ta ea).bind (matchTemplateExpr · tb eb)
    | _ => none
  | .and32 ta tb => match e with
    | .and32 ea eb => (matchTemplateExpr bindings ta ea).bind (matchTemplateExpr · tb eb)
    | _ => none
  | .or32 ta tb => match e with
    | .or32 ea eb => (matchTemplateExpr bindings ta ea).bind (matchTemplateExpr · tb eb)
    | _ => none
  | .xor32 ta tb => match e with
    | .xor32 ea eb => (matchTemplateExpr bindings ta ea).bind (matchTemplateExpr · tb eb)
    | _ => none
  | .add64 ta tb => match e with
    | .add64 ea eb => (matchTemplateExpr bindings ta ea).bind (matchTemplateExpr · tb eb)
    | _ => none
  | .sub64 ta tb => match e with
    | .sub64 ea eb => (matchTemplateExpr bindings ta ea).bind (matchTemplateExpr · tb eb)
    | _ => none
  | .xor64 ta tb => match e with
    | .xor64 ea eb => (matchTemplateExpr bindings ta ea).bind (matchTemplateExpr · tb eb)
    | _ => none
  | .and64 ta tb => match e with
    | .and64 ea eb => (matchTemplateExpr bindings ta ea).bind (matchTemplateExpr · tb eb)
    | _ => none
  | .or64 ta tb => match e with
    | .or64 ea eb => (matchTemplateExpr bindings ta ea).bind (matchTemplateExpr · tb eb)
    | _ => none
  | .shl64 ta tb => match e with
    | .shl64 ea eb => (matchTemplateExpr bindings ta ea).bind (matchTemplateExpr · tb eb)
    | _ => none
  | .shr64 ta tb => match e with
    | .shr64 ea eb => (matchTemplateExpr bindings ta ea).bind (matchTemplateExpr · tb eb)
    | _ => none
  | .mul64 ta tb => match e with
    | .mul64 ea eb => (matchTemplateExpr bindings ta ea).bind (matchTemplateExpr · tb eb)
    | _ => none
  | .mul32 ta tb => match e with
    | .mul32 ea eb => (matchTemplateExpr bindings ta ea).bind (matchTemplateExpr · tb eb)
    | _ => none
  | .not64 ta => match e with
    | .not64 ea => matchTemplateExpr bindings ta ea
    | _ => none
  | .sar64 ta tb => match e with
    | .sar64 ea eb => (matchTemplateExpr bindings ta ea).bind (matchTemplateExpr · tb eb)
    | _ => none
  | .sar32 ta tb => match e with
    | .sar32 ea eb => (matchTemplateExpr bindings ta ea).bind (matchTemplateExpr · tb eb)
    | _ => none
  | .not32 ta => match e with
    | .not32 ea => matchTemplateExpr bindings ta ea
    | _ => none
  | .ite tc tt tf => match e with
    | .ite ec et ef => (matchTemplateExpr bindings tc ec).bind (fun b => (matchTemplateExpr b tt et).bind (matchTemplateExpr · tf ef))
    | _ => none
  | .load tw tm ta => match e with
    | .load ew em ea =>
      if tw == ew then
        (matchTemplateMem bindings tm em).bind (matchTemplateExpr · ta ea)
      else none
    | _ => none

/-- Match a template memory against a ground memory. -/
def matchTemplateMem {Reg : Type} [DecidableEq Reg]
    (bindings : Std.HashMap HoleId (SymExpr Reg))
    (t : TemplateMem Reg) (m : SymMem Reg)
    : Option (Std.HashMap HoleId (SymExpr Reg)) :=
  match t, m with
  | .base, .base => some bindings
  | .store tw tm ta tv, .store ew em ea ev =>
    if tw == ew then
      (matchTemplateMem bindings tm em).bind fun b1 =>
      (matchTemplateExpr b1 ta ea).bind fun b2 =>
      matchTemplateExpr b2 tv ev
    else none
  | _, _ => none
end

/-- Match a template PC against a ground PC.
    Returns `some bindings` if the ground PC is an instance of the template. -/
def matchTemplatePC {Reg : Type} [DecidableEq Reg]
    (bindings : Std.HashMap HoleId (SymExpr Reg))
    (t : TemplatePC Reg) (pc : SymPC Reg)
    : Option (Std.HashMap HoleId (SymExpr Reg)) :=
  match t, pc with
  | .true, .true => some bindings
  | .eq ta tb, .eq ea eb =>
    (matchTemplateExpr bindings ta ea).bind (matchTemplateExpr · tb eb)
  | .lt ta tb, .lt ea eb =>
    (matchTemplateExpr bindings ta ea).bind (matchTemplateExpr · tb eb)
  | .le ta tb, .le ea eb =>
    (matchTemplateExpr bindings ta ea).bind (matchTemplateExpr · tb eb)
  | .and tφ tψ, .and eφ eψ =>
    (matchTemplatePC bindings tφ eφ).bind (matchTemplatePC · tψ eψ)
  | .not tφ, .not eφ => matchTemplatePC bindings tφ eφ
  | _, _ => none

/-- Check if a ground PC matches any known template (is an instance).
    Tries each template in order, returns true on first match. -/
def isTemplateInstance {Reg : Type} [DecidableEq Reg]
    (templates : Array (TemplatePC Reg)) (pc : SymPC Reg) : Bool :=
  templates.any fun t => (matchTemplatePC {} t pc).isSome

/-- Fast incremental stabilization using HashSet for O(1) membership.
    Single-threaded rip-indexed composition with inline dedup.
    Includes PC-signature equivalence class dedup and subsumption pruning. -/
def computeStabilizationHS {Reg : Type} [DecidableEq Reg] [Fintype Reg] [Hashable Reg] [EnumReg Reg] [BEq Reg] [ToString Reg]
    (ip_reg : Reg) (bodyArr : Array (Branch (SymSub Reg) (SymPC Reg)))
    (maxIter : Nat) (logFile : Option System.FilePath := none) : IO (Option (Nat × Nat)) := do
  let isa := vexSummaryISA Reg
  let initBranch := Branch.skip isa
  -- Extract the closure: all distinct atomic guard PCs from body branches.
  -- dataOnly=true filters rip-routing guards, keeping only data PCs (P₀).
  let (closure, ripCount, dataCount) := extractClosure ip_reg bodyArr (dataOnly := true)
  let mut current : Std.HashSet (Branch (SymSub Reg) (SymPC Reg)) := {}
  current := current.insert initBranch
  -- sigSeen tracks (sub, signature) classes across ALL iterations.
  -- A new branch is only added if its signature class hasn't been seen before.
  let mut sigSeen : Std.HashSet (SigDedupKey Reg) := {}
  let initSig := computePCSignature closure initBranch.pc
  -- initSigKey inserted after closedness check determines dedupSubHash
  let mut frontier : Array (Branch (SymSub Reg) (SymPC Reg) × Nat) := #[(initBranch, bodyArr.size)]
  -- allBranchesBySub: sub hash → array of branches, for efficient subsumption check
  let mut allBranchesBySub : Std.HashMap UInt64 (Array (Branch (SymSub Reg) (SymPC Reg))) := {}
  allBranchesBySub := allBranchesBySub.insert (hash initBranch.sub) #[initBranch]
  let log (msg : String) : IO Unit := do
    IO.println msg
    if let some path := logFile then
      let h ← IO.FS.Handle.mk path .append
      h.putStrLn msg
  log s!"  closure: total={ripCount + dataCount} rip={ripCount} data={dataCount} (using data-only={closure.size})"
  -- Collect registers referenced by data PCs (for projection/widening diagnostic)
  let mut dataPCRegs : Std.HashSet Reg := {}
  let mut dataPCsHaveLoads := false
  for pc in closure do
    dataPCRegs := SymPC.collectRegsHS pc dataPCRegs
    if SymPC.hasLoad pc then dataPCsHaveLoads := true
  let dataPCRegsArr := dataPCRegs.toArray
  log s!"  data PC regs (direct): [{", ".intercalate (dataPCRegsArr.toList.map toString)}] ({dataPCRegsArr.size} regs, loads={dataPCsHaveLoads})"
  -- Compute transitive closure of register dependency: if a projected register's
  -- body expression references reg R, R must also be projected (since R's value
  -- affects future projected values). Iterate until fixpoint.
  let mut closedRegs := dataPCRegs
  let mut closedNeedsMem := dataPCsHaveLoads
  let mut changed := true
  let mut closureRounds : Nat := 0
  while changed do
    changed := false
    closureRounds := closureRounds + 1
    for b in bodyArr do
      -- Check what each projected register's expression depends on
      let currentRegsArr := closedRegs.toArray
      for r in currentRegsArr do
        let exprRegs := SymExpr.collectRegsHS (b.sub.regs r) {}
        for er in exprRegs do
          unless closedRegs.contains er || er == ip_reg do
            closedRegs := closedRegs.insert er
            changed := true
      -- If we need memory, check what the mem expression depends on
      if closedNeedsMem then
        let memRegs := SymMem.collectRegsHS b.sub.mem {}
        for mr in memRegs do
          unless closedRegs.contains mr || mr == ip_reg do
            closedRegs := closedRegs.insert mr
            changed := true
      -- Check if any projected register's expression involves loads (adds mem dependency)
      unless closedNeedsMem do
        for r in currentRegsArr do
          if SymExpr.hasLoad (b.sub.regs r) then
            closedNeedsMem := true
            changed := true
  let closedRegsArr := closedRegs.toArray
  log s!"  closed projection: [{", ".intercalate (closedRegsArr.toList.map toString)}] ({closedRegsArr.size} regs, loads={closedNeedsMem}, rounds={closureRounds})"
  -- Helper: compute projection hash using the closed register set
  let projHashOf (sub : SymSub Reg) : UInt64 := Id.run do
    let mut h : UInt64 := 0
    for r in closedRegsArr do
      h := mixHash h (hash (sub.regs r))
    if closedNeedsMem then h := mixHash h (hash sub.mem)
    return h
  let dedupSubHash (sub : SymSub Reg) : UInt64 := projHashOf sub
  let initSigKey : SigDedupKey Reg := ⟨initBranch.sub, initSig⟩
  sigSeen := sigSeen.insert initSigKey
  let mut previousFrontier : Array (Branch (SymSub Reg) (SymPC Reg) × Nat) := #[]
  -- Template-based dedup: activated when explosion is detected
  let mut templates : Array (TemplatePC Reg) := #[]
  let mut templatesActive := false
  let explosionThreshold : Nat := 3  -- trigger when composed > threshold × frontier
  for k in List.range maxIter do
    let t_start ← IO.monoMsNow
    previousFrontier := frontier
    let (composed, pairsComposed, skipped, dropped) :=
      composeBranchArrayIndexed ip_reg bodyArr (frontier.map (·.1))
    -- Template extraction: detect explosion and extract templates
    let mut templateCollapsed : Nat := 0
    if !templatesActive && previousFrontier.size > 0 &&
       composed.size > explosionThreshold * previousFrontier.size then
      -- Explosion detected: anti-unify consecutive-round PCs to find templates
      let pcPairsForAU := pairFrontierPCs previousFrontier composed
      let newTemplates := extractTemplatesFromPairs pcPairsForAU
      if newTemplates.size > 0 then
        templates := templates ++ newTemplates
        templatesActive := true
        let totalHoles := newTemplates.foldl (fun acc t => acc + t.holeCount) 0
        log s!"    TEMPLATES ACTIVATED: {newTemplates.size} templates, {totalHoles} total holes (explosion: {composed.size} > {explosionThreshold}×{previousFrontier.size})"
    -- Inline dedup: exact-match via HashSet + signature-class via sigSeen
    -- Template dedup runs first when active (before signature dedup)
    let mut newBranches : Array (Branch (SymSub Reg) (SymPC Reg) × Nat) := #[]
    let mut dupes : Nat := 0
    let mut sigCollapsed : Nat := 0
    for (b, bodyIdx) in composed do
      if current.contains b then
        dupes := dupes + 1
      else if templatesActive && isTemplateInstance templates b.pc then
        -- PC matches a known template — collapse (don't add to frontier)
        templateCollapsed := templateCollapsed + 1
      else
        -- Check signature-class dedup (uses projection hash if closed)
        let sig := computePCSignature closure b.pc
        let key : SigDedupKey Reg := ⟨b.sub, sig⟩
        if sigSeen.contains key then
          sigCollapsed := sigCollapsed + 1
        else
          sigSeen := sigSeen.insert key
          newBranches := newBranches.push (b, bodyIdx)
    -- Semantic subsumption via SMT: batch check new branches against existing
    let t_prune_start ← IO.monoMsNow
    let mut prunedCount : Nat := 0
    -- Build (stronger_pc, weaker_pc) pairs and track which new branch each belongs to
    let mut pcPairs : Array (SymPC Reg × SymPC Reg) := #[]
    let mut queryBranchIdx : Array Nat := #[]
    let mut branchIdx : Nat := 0
    for (bi, _) in newBranches do
      let h := hash bi.sub
      let existingGroup := allBranchesBySub.getD h #[]
      for bj in existingGroup do
        if bi.pc != bj.pc then
          pcPairs := pcPairs.push (bi.pc, bj.pc)
          queryBranchIdx := queryBranchIdx.push branchIdx
      branchIdx := branchIdx + 1
    -- Call CVC5 with caching (Green-style)
    let mut subsumedSet : Std.HashSet Nat := {}
    if pcPairs.size > 0 then
      let subsCache ← IO.mkRef ({} : SMTCache Reg)
      let (subsResults, subsHits) ← smtCheckImplCached subsCache pcPairs ".lake/smt_subsumption.smt2"
      for i in [:subsResults.size] do
        if h : i < subsResults.size then
          if subsResults[i] then
            if h2 : i < queryBranchIdx.size then
              subsumedSet := subsumedSet.insert queryBranchIdx[i]
      log s!"    smt: {pcPairs.size} queries, cache_hits={subsHits}, {subsumedSet.size} subsumed"
    -- Filter new branches
    let mut survivingNew : Array (Branch (SymSub Reg) (SymPC Reg) × Nat) := #[]
    branchIdx := 0
    for bi in newBranches do
      if subsumedSet.contains branchIdx then
        prunedCount := prunedCount + 1
      else
        survivingNew := survivingNew.push bi
      branchIdx := branchIdx + 1
    newBranches := survivingNew
    -- Update tracking structures with surviving new branches
    for (b, _) in newBranches do
      current := current.insert b
      let h := hash b.sub
      let arr := allBranchesBySub.getD h #[]
      allBranchesBySub := allBranchesBySub.insert h (arr.push b)
    let t_end ← IO.monoMsNow
    -- Count distinct subs in frontier (diagnostic: how many "paths"?)
    let mut frontierSubs : Std.HashSet UInt64 := {}
    let mut frontierSubsNoRip : Std.HashSet UInt64 := {}
    let mut projectedSubs : Std.HashSet UInt64 := {}
    for (b, _) in newBranches do
      frontierSubs := frontierSubs.insert (hash b.sub)
      let noRipSub : SymSub Reg := { b.sub with regs := fun r => if r == ip_reg then .const 0 else b.sub.regs r }
      frontierSubsNoRip := frontierSubsNoRip.insert (hash noRipSub)
      -- Project sub onto closed projection registers
      projectedSubs := projectedSubs.insert (projHashOf b.sub)
    log s!"  K={k}: |S|={current.size} |frontier|={frontier.size} |new|={newBranches.size} |distinct_subs|={frontierSubs.size} |no_rip|={frontierSubsNoRip.size} |proj|={projectedSubs.size} pairs={pairsComposed} skipped={skipped} dropped={dropped} dupes={dupes} sig_collapsed={sigCollapsed} pruned={prunedCount} templates_active={templatesActive} n_templates={templates.size} template_collapsed={templateCollapsed} compose={t_prune_start - t_start}ms prune={t_end - t_prune_start}ms total={t_end - t_start}ms"
    if newBranches.size == 0 then
      return some (k, current.size)
    frontier := newBranches
  return none

/-! ## Stabilization Computation -/

/-- Naive stabilization: composes bodyDenot with the FULL accumulated set each
    iteration. Kept for correctness comparison. -/
def computeStabilizationNaive {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (bodyDenot : Finset (Branch (SymSub Reg) (SymPC Reg)))
    (maxIter : Nat) : IO (Option (Nat × Nat)) := do
  let isa := vexSummaryISA Reg
  let mut current : Finset (Branch (SymSub Reg) (SymPC Reg)) := {Branch.skip isa}
  for k in List.range maxIter do
    let composed := composeBranchFinsetsSimplified bodyDenot current
    let next := current ∪ composed
    if k % 5 == 0 || next == current then
      IO.println s!"  K={k}: |S| = {current.card}, |new| = {(next \ current).card}"
    if next == current then
      return some (k, current.card)
    current := next
  return none

/-- Incremental stabilization: only composes bodyDenot with the frontier
    (branches added in the previous round), not the full accumulated set.

    Correctness: composition distributes over union in the second argument.
    If `current = old ∪ frontier`, then `body ⊗ current = (body ⊗ old) ∪ (body ⊗ frontier)`.
    Since `body ⊗ old ⊆ current` (computed in prior rounds), only `body ⊗ frontier`
    can produce genuinely new branches. -/
def computeStabilization {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (bodyDenot : Finset (Branch (SymSub Reg) (SymPC Reg)))
    (maxIter : Nat) (logFile : Option System.FilePath := none) : IO (Option (Nat × Nat)) := do
  let isa := vexSummaryISA Reg
  let init : Finset (Branch (SymSub Reg) (SymPC Reg)) := {Branch.skip isa}
  let mut current := init
  let mut frontier := init
  let log (msg : String) : IO Unit := do
    IO.println msg
    if let some path := logFile then
      let h ← IO.FS.Handle.mk path .append
      h.putStrLn msg
  for k in List.range maxIter do
    let t_start ← IO.monoMsNow
    let composed := composeBranchFinsetsSimplified bodyDenot frontier
    let t_compose ← IO.monoMsNow
    let newBranches := composed \ current
    let t_diff ← IO.monoMsNow
    log s!"  K={k}: |S|={current.card} |frontier|={frontier.card} |composed|={composed.card} |new|={newBranches.card} compose={t_compose - t_start}ms diff={t_diff - t_compose}ms"
    if newBranches.card == 0 then
      return some (k, current.card)
    current := current ∪ newBranches
    frontier := newBranches
  return none

/-! ## Dispatch Body Construction -/

/-- Build the dispatch body CompTree from a list of (address, block) pairs.
    Each block is guarded by `rip == address`. -/
def buildDispatchBody {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (ip_reg : Reg) (blocks : List (UInt64 × Block Reg)) :
    CompTree (SymSub Reg) (SymPC Reg) :=
  blocks.foldr (fun (addr, block) acc =>
    CompTree.guardedChoice
      (SymPC.eq (SymExpr.reg ip_reg) (SymExpr.const addr))
      (blockToCompTree block)
      acc)
    CompTree.skip

/-- Compute bodyDenot as a flat union of per-block branches with rip guards.
    Avoids the nested negation chains from `denot` on nested guardedChoice. -/
def flatBodyDenot {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (ip_reg : Reg) (blocks : List (UInt64 × Block Reg)) :
    Finset (Branch (SymSub Reg) (SymPC Reg)) :=
  let isa := vexSummaryISA Reg
  blocks.foldl (fun acc (addr, block) =>
    let blockDenot := CompTree.denot isa (blockToCompTree block)
    let guard : Branch (SymSub Reg) (SymPC Reg) :=
      ⟨isa.id_sub, SymPC.eq (SymExpr.reg ip_reg) (SymExpr.const addr)⟩
    acc ∪ composeBranchFinsets isa {guard} blockDenot)
    ∅

/-- Convert Finset to Array at runtime. Multiset is Quot (List.Perm),
    which is erased to List at runtime. unsafeCast recovers it. -/
unsafe def finsetToArrayImpl {α : Type} (s : Finset α) : Array α :=
  (unsafeCast s.val : List α).toArray

@[implemented_by finsetToArrayImpl]
def finsetToArray {α : Type} (s : Finset α) : Array α :=
  #[]

/-- Array-based variant of flatBodyDenot — avoids Finset DecidableEq overhead
    that causes hangs on blocks with large symbolic terms (e.g., 22-store chains).
    Produces the same branches but without dedup (callers don't need it — downstream
    dedup happens via HashSet in computeFunctionStabilization). -/
def flatBodyDenotArray {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (ip_reg : Reg) (blocks : List (UInt64 × Block Reg)) :
    Array (Branch (SymSub Reg) (SymPC Reg)) := Id.run do
  let isa := vexSummaryISA Reg
  let mut result : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]
  for (addr, block) in blocks do
    let blockDenot := CompTree.denot isa (blockToCompTree block)
    let guard : Branch (SymSub Reg) (SymPC Reg) :=
      ⟨isa.id_sub, SymPC.eq (SymExpr.reg ip_reg) (SymExpr.const addr)⟩
    for b in finsetToArray blockDenot do
      result := result.push (guard.compose isa b)
  return result

/-! ## Parse blocks with addresses -/

/-- Parse block strings into (address, block) pairs. -/
def parseBlocksWithAddresses (blockStrs : List String) :
    Except String (List (UInt64 × Block Amd64Reg)) :=
  blockStrs.mapM fun text => do
    let ip ← extractIMarkIP text
    let block ← parseIRSB text
    return (ip, block)

/-! ## JSON Block Loading

Load VEX IR blocks from JSON files. Supports two formats:
1. Flat format: `{"arch": "amd64", "blocks": ["IRSB {...}", ...]}`
2. Per-function format: `{"arch": "amd64", "functions": {"name": {"addr": "0x...", "size": N, "blocks": [...]}, ...}}`
The flat format comes from pyvex linear sweep. The per-function format is the
legacy format from `reference/tinyc/parser_nt_blocks.json`. -/

/-- Load a flat list of IRSB strings from a JSON file.
    Accepts both flat format (blocks array) and per-function format (concatenates all blocks). -/
def loadBlocksFromJSON (path : System.FilePath) : IO (Array String) := do
  let contents ← IO.FS.readFile path
  match Lean.Json.parse contents with
  | .error e => throw (IO.userError s!"JSON parse error in {path}: {e}")
  | .ok json =>
    -- Try flat format first: {"blocks": [...]}
    match json.getObjValAs? (α := Array String) "blocks" with
    | .ok blocks => return blocks
    | .error _ =>
      -- Try per-function format: {"functions": {"name": {"blocks": [...]}}}
      match json.getObjVal? "functions" with
      | .error _ => throw (IO.userError s!"JSON has neither 'blocks' nor 'functions' key")
      | .ok funcsJson =>
        match funcsJson with
        | .obj funcsObj =>
          let mut allBlocks : Array String := #[]
          for (_, funcJson) in funcsObj.toArray do
            match funcJson.getObjValAs? (α := Array String) "blocks" with
            | .ok blocks => allBlocks := allBlocks ++ blocks
            | .error e => throw (IO.userError s!"Error reading function blocks: {e}")
          return allBlocks
        | _ => throw (IO.userError s!"'functions' value is not an object")

/-! ## Stratified Fixpoint — Per-Function Summaries

Instead of treating all blocks as one flat dispatch loop, compute fixpoints
bottom-up along the call graph:
1. Leaf functions (next_sym) first — no outgoing calls to other parser functions
2. NT functions (term, sum, test, expr, paren_expr, statement) — call next_sym
   and each other via mutual recursion

At each composition step, when a frontier branch's rip target matches another
function's entry address, compose with that function's current summary instead
of its individual blocks. This prevents cross-function path explosion. -/

/-- A function in the stratified fixpoint. -/
structure FunctionSpec where
  name : String
  entryAddr : UInt64
  blocks : List String  -- raw IRSB strings
  deriving Inhabited

/-- Parse a hex address string (with or without 0x prefix) to UInt64. -/
def parseHexAddr (s : String) : Option UInt64 :=
  let digits := if s.startsWith "0x" || s.startsWith "0X" then s.drop 2 else s
  digits.foldl (fun acc c =>
    acc.bind fun n =>
      if '0' ≤ c && c ≤ '9' then some (n * 16 + (c.toNat - '0'.toNat))
      else if 'a' ≤ c && c ≤ 'f' then some (n * 16 + (c.toNat - 'a'.toNat + 10))
      else if 'A' ≤ c && c ≤ 'F' then some (n * 16 + (c.toNat - 'A'.toNat + 10))
      else none) (some 0)
  |>.map UInt64.ofNat

/-- Parse memory regions from JSON array.
    Format: `[{"name": "...", "vaddr": "0x...", "size": N, "flags": "..."}, ...]` -/
private def parseMemRegions (json : Lean.Json) : IO (Array MemRegion) := do
  match json.getArr? with
  | .error e => throw (IO.userError s!"memory_regions is not an array: {e}")
  | .ok arr =>
    let mut regions : Array MemRegion := #[]
    for item in arr do
      let name ← match item.getObjValAs? (α := String) "name" with
        | .ok s => pure s
        | .error e => throw (IO.userError s!"region missing name: {e}")
      let vaddrStr ← match item.getObjValAs? (α := String) "vaddr" with
        | .ok s => pure s
        | .error e => throw (IO.userError s!"region missing vaddr: {e}")
      let vaddr ← match parseHexAddr vaddrStr with
        | some a => pure a
        | none => throw (IO.userError s!"bad region vaddr: {vaddrStr}")
      let size ← match item.getObjValAs? (α := Nat) "size" with
        | .ok n => pure n
        | .error e => throw (IO.userError s!"region missing size: {e}")
      let flags ← match item.getObjValAs? (α := String) "flags" with
        | .ok s => pure s
        | .error _ => pure ""  -- flags optional
      regions := regions.push ⟨name, vaddr, size, flags⟩
    return regions

/-- Load per-function specs from legacy JSON format.
    Format: `{"functions": {"name": {"addr": "0x...", "size": N, "blocks": [...]}, ...},
              "memory_regions": [...]}` -/
def loadFunctionsFromJSON (path : System.FilePath) : IO (Array FunctionSpec × Array MemRegion) := do
  let contents ← IO.FS.readFile path
  match Lean.Json.parse contents with
  | .error e => throw (IO.userError s!"JSON parse error in {path}: {e}")
  | .ok json =>
    -- Parse memory regions (optional — absent in older JSON files)
    let regions ← match json.getObjVal? "memory_regions" with
      | .ok regionsJson => parseMemRegions regionsJson
      | .error _ => pure #[]
    match json.getObjVal? "functions" with
    | .error _ => throw (IO.userError s!"JSON has no 'functions' key (not per-function format)")
    | .ok funcsJson =>
      match funcsJson with
      | .obj funcsObj =>
        let mut specs : Array FunctionSpec := #[]
        for (name, funcJson) in funcsObj.toArray do
          let addrStr ← match funcJson.getObjValAs? (α := String) "addr" with
            | .ok s => pure s
            | .error e => throw (IO.userError s!"Missing addr for {name}: {e}")
          let addr ← match parseHexAddr addrStr with
            | some a => pure a
            | none =>
              match addrStr.toNat? with
              | some n => pure (UInt64.ofNat n)
              | none => throw (IO.userError s!"Bad address for {name}: {addrStr}")
          let blocks ← match funcJson.getObjValAs? (α := Array String) "blocks" with
            | .ok bs => pure bs.toList
            | .error e => throw (IO.userError s!"Missing blocks for {name}: {e}")
          specs := specs.push ⟨name, addr, blocks⟩
        return (specs, regions)
      | _ => throw (IO.userError s!"'functions' value is not an object")

/-- Result of function discovery: specs + count of orphan blocks not in any symbol. -/
structure DiscoveryResult where
  functions : Array FunctionSpec
  orphanCount : Nat
  deriving Inhabited

def discoverFunctions (blocks : Array String) (symbols : Array (String × UInt64 × UInt64)) :
    Except String DiscoveryResult := do
  -- Extract entry address from each block
  let mut blockAddrs : Array (UInt64 × String) := #[]
  for blockStr in blocks do
    let addr ← extractIMarkIP blockStr
    blockAddrs := blockAddrs.push (addr, blockStr)
  -- Sort symbols by address for deterministic output
  let sortedSyms := symbols.qsort fun (_, a1, _) (_, a2, _) => a1 < a2
  -- Assign blocks to symbols
  let mut result : Array FunctionSpec := #[]
  let mut assignedCount : Nat := 0
  for (name, addr, size) in sortedSyms do
    let funcBlocks := blockAddrs.filter fun (blockAddr, _) =>
      blockAddr >= addr && blockAddr < addr + size
    -- Sort blocks by address within each function
    let sortedBlocks := funcBlocks.qsort fun (a1, _) (a2, _) => a1 < a2
    let blockStrs := sortedBlocks.map (·.2) |>.toList
    if !blockStrs.isEmpty then
      result := result.push ⟨name, addr, blockStrs⟩
      assignedCount := assignedCount + sortedBlocks.size
  let orphanCount := blockAddrs.size - assignedCount
  return ⟨result, orphanCount⟩

/-- Compose body branches with frontier, but when a body branch's rip target
    matches a function entry, substitute that function's summary branches
    instead of continuing through individual blocks.

    For a body branch B with rip target = function F's entry:
    - Compose B with each branch in F's summary
    - The summary branch has rip = return address (wherever F returns to)
    - Result: caller's pre-call work + F's full behavior + return to caller

    Returns (result, pairsComposed, skipped, dropped, summaryHits). -/
def composeBranchArrayStratified {Reg : Type} [DecidableEq Reg] [Fintype Reg] [BEq Reg]
    (ip_reg : Reg)
    (bodyArr frontierArr : Array (Branch (SymSub Reg) (SymPC Reg)))
    (summaries : Std.HashMap UInt64 (Array (Branch (SymSub Reg) (SymPC Reg)))) :
    Array (Branch (SymSub Reg) (SymPC Reg)) × Nat × Nat × Nat × Nat := Id.run do
  let isa := vexSummaryISA Reg
  -- Build frontier index by rip guard
  let mut frontierByRip : Std.HashMap UInt64 (Array (Branch (SymSub Reg) (SymPC Reg))) := {}
  let mut frontierNoRip : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]
  for f in frontierArr do
    match extractRipGuard ip_reg f.pc with
    | some addr =>
      let arr := frontierByRip.getD addr #[]
      frontierByRip := frontierByRip.insert addr (arr.push f)
    | none => frontierNoRip := frontierNoRip.push f
  -- Compose using index + summary substitution
  let mut result : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]
  let mut dropped : Nat := 0
  let mut composed_count : Nat := 0
  let mut summaryHits : Nat := 0
  let totalPairs := bodyArr.size * frontierArr.size
  for b in bodyArr do
    match extractRipTarget ip_reg b.sub with
    | some target =>
      -- Check if this target is a function entry with a summary
      match summaries.get? target with
      | some summaryBranches =>
        -- Summary substitution: compose this body branch with callee's summary
        summaryHits := summaryHits + 1
        for sb in summaryBranches do
          composed_count := composed_count + 1
          let composed := b.compose isa sb
          match simplifyBranch composed with
          | none => dropped := dropped + 1
          | some b' => result := result.push b'
      | none =>
        -- Normal rip-indexed composition
        let compatible := (frontierByRip.getD target #[]) ++ frontierNoRip
        for f in compatible do
          composed_count := composed_count + 1
          let composed := b.compose isa f
          match simplifyBranch composed with
          | none => dropped := dropped + 1
          | some b' => result := result.push b'
    | none =>
      -- Can't determine target, fall back to all frontier branches
      for f in frontierArr do
        composed_count := composed_count + 1
        let composed := b.compose isa f
        match simplifyBranch composed with
        | none => dropped := dropped + 1
        | some b' => result := result.push b'
  let skipped := totalPairs - composed_count
  return (result, composed_count, skipped, dropped, summaryHits)

/-- Pool for deduplicating SymSub values across branches.
    When multiple branches share identical substitutions (same register map +
    memory chain), they can point to a single pooled copy. The pool uses hash
    lookup with equality check to avoid collisions. -/
structure SubPool (Reg : Type) [Hashable Reg] [EnumReg Reg] where
  pool : Std.HashMap UInt64 (SymSub Reg) := {}
  hits : Nat := 0
  misses : Nat := 0

/-- Intern a SymSub: if an equal sub is already pooled, return the pooled copy
    (sharing its heap allocation). Otherwise, insert and return the new sub.
    On hash collision with a non-equal sub, the new sub is stored (overwriting
    the old entry — a minor loss of sharing, not a correctness issue). -/
def SubPool.intern {Reg : Type} [DecidableEq Reg] [Fintype Reg] [Hashable Reg] [EnumReg Reg]
    (sp : SubPool Reg) (sub : SymSub Reg) : SymSub Reg × SubPool Reg :=
  let h := hash sub
  match sp.pool.get? h with
  | some existing =>
    if existing == sub
    then (existing, { sp with hits := sp.hits + 1 })
    else (sub, { sp with pool := sp.pool.insert h sub, misses := sp.misses + 1 })
  | none => (sub, { sp with pool := sp.pool.insert h sub, misses := sp.misses + 1 })

