import Instances.ISAs.VexCompTree
import Instances.ISAs.VexProofCompression
import Instances.ISAs.NextSymParserTest
import Instances.ISAs.ParserNTParserTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA VexIRParser

/-!
# DispatchLoopEval — Empirical stabilization of dispatch loop branch sets

Builds a dispatch body CompTree from parsed VEX blocks, then iterates
`loopBranchSet`-style composition until the branch set stabilizes.

Includes a PC simplifier that evaluates constant-constant comparisons,
preventing syntactic noise from blocking convergence detection.
-/

/-! ## PC Simplifier

After composition, PCs may contain `eq(const a, const b)` terms from
substituting rip-routing guards. These are trivially true or false but
NOT simplified by the symbolic algebra. The simplifier evaluates them,
dropping unsatisfiable branches and collapsing trivially-true conjuncts. -/

/-- Simplify a SymPC by evaluating constant-constant comparisons.
    Returns `none` if the PC is unsatisfiable (should drop the branch). -/
partial def SymPC.simplifyConst {Reg : Type} : SymPC Reg → Option (SymPC Reg)
  | .true => some .true
  | .eq (.const a) (.const b) => if a == b then some .true else none
  | .lt (.const a) (.const b) =>
      if (a.toNat + 2^63) % 2^64 < (b.toNat + 2^63) % 2^64 then some .true else none
  | .le (.const a) (.const b) =>
      if (a.toNat + 2^63) % 2^64 ≤ (b.toNat + 2^63) % 2^64 then some .true else none
  | .eq l r => some (.eq l r)
  | .lt l r => some (.lt l r)
  | .le l r => some (.le l r)
  | .and φ ψ =>
      match (SymPC.simplifyConst φ, SymPC.simplifyConst ψ) with
      | (none, _) | (_, none) => none
      | (some .true, some ψ') => some ψ'
      | (some φ', some .true) => some φ'
      | (some φ', some ψ') => some (.and φ' ψ')
  | .not φ =>
      match SymPC.simplifyConst φ with
      | none => some .true
      | some .true => none
      | some φ' => some (.not φ')

/-- Simplify a branch's PC. Returns `none` if unsatisfiable. -/
def simplifyBranch {Sub : Type*} {Reg : Type} (b : Branch Sub (SymPC Reg)) :
    Option (Branch Sub (SymPC Reg)) :=
  match SymPC.simplifyConst b.pc with
  | none => none
  | some pc' => some ⟨b.sub, pc'⟩

/-! ## Simplified Composition

Compose two branch Finsets and simplify, dropping unsatisfiable branches. -/

/-- Compose + simplify: compose all pairs, then simplify PCs and drop
    branches with unsatisfiable constant-constant comparisons. -/
def composeBranchFinsetsSimplified {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (B₁ B₂ : Finset (Branch (SymSub Reg) (SymPC Reg))) :
    Finset (Branch (SymSub Reg) (SymPC Reg)) :=
  let raw := composeBranchFinsets (vexSummaryISA Reg) B₁ B₂
  -- filterMap: apply simplifyBranch, keep only Some results
  raw.biUnion (fun b =>
    match simplifyBranch b with
    | none => ∅
    | some b' => {b'})

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
    Array (Branch (SymSub Reg) (SymPC Reg)) × Nat × Nat × Nat := Id.run do
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
  -- Compose using index
  let mut result : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]
  let mut dropped : Nat := 0
  let mut composed_count : Nat := 0
  let totalPairs := bodyArr.size * frontierArr.size
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
      | some b' => result := result.push b'
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
  let ripIndex ← do
    let mut byRip : Std.HashMap UInt64 (Array (Branch (SymSub Reg) (SymPC Reg))) := {}
    let mut noRip : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]
    for f in frontierArr do
      match extractRipGuard ip_reg f.pc with
      | some addr =>
        let arr := byRip.getD addr #[]
        byRip := byRip.insert addr (arr.push f)
      | none => noRip := noRip.push f
    return (byRip, noRip)
  let (frontierByRip, frontierNoRip) := ripIndex
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

/-- Fast incremental stabilization using HashSet for O(1) membership.
    Uses parallel rip-indexed composition — splits body across N workers. -/
def computeStabilizationHS {Reg : Type} [DecidableEq Reg] [Fintype Reg] [Hashable Reg] [EnumReg Reg] [BEq Reg]
    (ip_reg : Reg) (bodyArr : Array (Branch (SymSub Reg) (SymPC Reg)))
    (maxIter : Nat) (logFile : Option System.FilePath := none) : IO (Option (Nat × Nat)) := do
  let isa := vexSummaryISA Reg
  let initBranch := Branch.skip isa
  let mut current : Std.HashSet (Branch (SymSub Reg) (SymPC Reg)) := {}
  current := current.insert initBranch
  let mut frontier : Array (Branch (SymSub Reg) (SymPC Reg)) := #[initBranch]
  let log (msg : String) : IO Unit := do
    IO.println msg
    if let some path := logFile then
      let h ← IO.FS.Handle.mk path .append
      h.putStrLn msg
  for k in List.range maxIter do
    let t_start ← IO.monoMsNow
    let (newBranches, current', pairsComposed, skipped, dropped, dupes) ←
      composeAndDedupParallel ip_reg bodyArr frontier current
    current := current'
    let t_end ← IO.monoMsNow
    log s!"  K={k}: |S|={current.size} |frontier|={frontier.size} |new|={newBranches.size} pairs={pairsComposed} skipped={skipped} dropped={dropped} dupes={dupes} time={t_end - t_start}ms"
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
private unsafe def finsetToArrayImpl {α : Type} (s : Finset α) : Array α :=
  (unsafeCast s.val : List α).toArray

@[implemented_by finsetToArrayImpl]
private def finsetToArray {α : Type} (s : Finset α) : Array α :=
  #[]

/-! ## Parse blocks with addresses -/

/-- Parse block strings into (address, block) pairs. -/
def parseBlocksWithAddresses (blockStrs : List String) :
    Except String (List (UInt64 × Block Amd64Reg)) :=
  blockStrs.mapM fun text => do
    let ip ← extractIMarkIP text
    let block ← parseIRSB text
    return (ip, block)

/-! ## Run stabilization on next_sym -/

#eval do
  let logPath : System.FilePath := ".lake/stabilization.log"
  IO.FS.writeFile logPath ""
  let log (msg : String) : IO Unit := do
    IO.println msg
    let h ← IO.FS.Handle.mk logPath .append
    h.putStrLn msg
  log "=== Dispatch Loop Stabilization: next_sym (60 blocks) ==="
  match parseBlocksWithAddresses nextSymBlocks with
  | .error e => log s!"PARSE ERROR: {e}"
  | .ok allPairs =>
    log s!"Total blocks available: {allPairs.length}"
    log "N, |bodyDenot|, K, |S_final|, bodyDenot_ms, stabilization_ms"
    for n in [60] do
      if n > allPairs.length then
        log s!"{n}, ---, SKIP (only {allPairs.length} blocks), ---, ---, ---"
      else
        let pairs := allPairs.take n
        let t0 ← IO.monoMsNow
        let body := flatBodyDenot Amd64Reg.rip pairs
        let t1 ← IO.monoMsNow
        let bodyArr := finsetToArray body
        log s!"  N={n}: |bodyDenot|={bodyArr.size}, starting stabilization..."
        match ← computeStabilizationHS Amd64Reg.rip bodyArr 200 logPath with
        | some (k, card) =>
          let t2 ← IO.monoMsNow
          log s!"{n}, {body.card}, {k}, {card}, {t1 - t0}, {t2 - t1}"
        | none =>
          let t2 ← IO.monoMsNow
          log s!"{n}, {body.card}, DNF, DNF, {t1 - t0}, {t2 - t1}"
