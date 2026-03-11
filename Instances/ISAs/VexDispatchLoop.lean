import Instances.ISAs.VexWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

/-!
# Dispatch Loop Body Path Realizability

The key theorem for interprocedural grammar extraction from mutually
recursive CFG parsers.

## Architecture

A **dispatch loop** treats an entire program as a single while loop:

```
while rip ∈ block_ips { execute block at rip }
```

The CompTree body is a nested `guardedChoice` selecting the right block
by rip value. This works for mutually recursive parsers because
`BranchClassesStable` operates on **PC signatures** — which character-class
conditions hold — not on full concrete state including stack depth.

Two states at different call depths reading the same character have
identical PC signatures. So `BranchClassesStable` holds with `K = 2^|closure|`,
determined by the finite variety of grammar conditions, not recursion depth.

## What This File Proves

`dispatch_bodyPathStepRealizable` is proved here: for every concrete state `s`,
the block at `rip(s)` constitutes a valid body-path representative for
`bodyEffect s`. This connects "we have all the blocks" to "the dispatch loop
machinery applies."

The convergence chain downstream — `BranchClassesStable` →
`whileBranchingLoopWitnessComplete_of_branchClassesStable` →
`extractedModel_of_witnessComplete` — is already proved in the framework and
applies once the preconditions are supplied.

## What Is Still Needed

Three things remain before the full interprocedural grammar extraction pipeline
is closed:

1. **`BranchClassesStable` instantiation** — the stability theorem must be
   instantiated for the dispatch loop body concretely, with `closure` drawn
   from the actual PC conditions of the block set.

2. **`hStep` derivation** — the hypothesis `∀ s, ∃ b ∈ allBlocks, bodyEffect s ∈ execBlockSuccs b s`
   must be derived from the dispatch-loop body construction, not merely assumed.
   This requires showing the body always selects the block matching `rip(s)`.

3. **PC-signature independence from call depth** — an intermediate lemma is
   needed showing that `pcSignatureWith ... closure s` depends only on the
   character-class conditions in `s`, not on stack depth or call frame. This
   is what makes the orbit finite even for recursive parsers.

These three items are the remaining proof obligations. `dispatch_bodyPathStepRealizable`
is a key bridge lemma, but not the only one.

## Connection to STALAGMITE and the Learnability Framework

From `CircularCoinduction.lean` line 41:
  "Stubs in stalagmite ARE loop summaries. Co-refinement IS circular
  coinduction."

The dispatch loop body effect IS a Sharir-Pnueli functional summary
for each NT in the call graph. Composition at call sites follows
from the sequential composition of summaries already proved in
`VexProgram.lean`. `BodyPathStepRealizable` is the bridge between
the concrete execution and the symbolic summary witness required by
the framework.
-/

/-! ## Single-Block Path Simplification -/

/-- For a single-block path, `execBlockPath [b] s = execBlockSuccs b s`.

    The path executes one block and stops; the result is exactly the
    concrete successors of that one block. -/
theorem execBlockPath_singleton
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (b : Block Reg) (s : ConcreteState Reg) :
    execBlockPath [b] s = execBlockSuccs b s := by
  ext x
  simp only [execBlockPath, Finset.mem_biUnion, Finset.mem_singleton]
  constructor
  · rintro ⟨mid, hmid, rfl⟩; exact hmid
  · intro hx; exact ⟨x, hx, rfl⟩

/-! ## Dispatch Loop Body Path Realizability -/

section DispatchBodyPathRealizable

variable {Reg : Type}
variable [DecidableEq Reg] [Fintype Reg]
variable [∀ (s : ConcreteState Reg) (φ : SymPC Reg),
  Decidable ((vexSummaryISA Reg).satisfies s φ)]

/-- **The core dispatch loop theorem.**

    For any `VexLoopSummary` whose `bodyEffect` is implemented by some
    block in `allBlocks` (concretely: `bodyEffect s ∈ execBlockSuccs b s`
    for some `b ∈ allBlocks`), `BodyPathStepRealizable` holds for the
    single-block path family `{[b] | b ∈ allBlocks}`.

    **Proof sketch:**
    1. From `hStep`, find the executing block `b` for state `s`.
    2. `bodyEffect s ∈ execBlockSuccs b s = summarySuccs (lowerBlockPathSummaries [b]) s`
       (via `summarySuccs_lowerBlockPathSummaries_eq_execBlockPath`).
    3. Extract a witnessing summary `σ ∈ lowerBlockPathSummaries [b]`
       with `Summary.enabled σ s` and `Summary.apply σ s = bodyEffect s`.
    4. Build `LiveBranchClass { path := [b], summary := σ, ... }` and
       verify all six conditions of `RealizesBodyStep`.

    This is a key bridge lemma for the interprocedural grammar extraction
    pipeline. The downstream chain (`BranchClassesStable` → orbit cycling →
    `whileBranchingLoopWitnessComplete` → `extractedModel`) is already proved
    in the framework, but three further items are still needed before the
    pipeline closes: `BranchClassesStable` instantiated for the dispatch loop,
    `hStep` derived from the body construction, and a PC-signature independence
    lemma ruling out call-depth sensitivity. See the module docstring. -/
theorem dispatch_bodyPathStepRealizable
    (loop : VexLoopSummary Reg)
    (allBlocks : Finset (Block Reg))
    (closure : Finset (SymPC Reg))
    (hStep : ∀ s, ∃ b ∈ allBlocks, loop.bodyEffect s ∈ execBlockSuccs b s) :
    BodyPathStepRealizable loop (allBlocks.image (fun b => [b])) closure := by
  intro s
  -- Step 1: find the executing block for this state
  obtain ⟨b, hbMem, hbEffect⟩ := hStep s
  -- Step 2: translate into summarySuccs language
  have hInSuccs : loop.bodyEffect s ∈ summarySuccs (lowerBlockPathSummaries [b]) s := by
    rw [summarySuccs_lowerBlockPathSummaries_eq_execBlockPath, execBlockPath_singleton]
    exact hbEffect
  -- Step 3: extract the witnessing summary
  rw [mem_summarySuccs, summaryDenotes_iff] at hInSuccs
  obtain ⟨σ, hσMem, hσEnabled, hσApply⟩ := hInSuccs
  -- Step 4: build LiveBranchClass and verify RealizesBodyStep
  refine ⟨{ path := [b], summary := σ,
             signature := pcSignatureWith (vexSummaryISA Reg) closure s }, ?_⟩
  refine ⟨⟨Finset.mem_image.mpr ⟨b, hbMem, rfl⟩, hσMem, hσEnabled, rfl⟩,
          hσApply, ?_⟩
  rw [execBlockPath_singleton]
  exact hbEffect

end DispatchBodyPathRealizable

/-! ## Concrete Successor Determinism -/

/-- `execStmtsSuccs` always returns exactly one concrete successor.

    The concrete semantics is deterministic: a branch statement either fires or
    doesn't (both conditions are decidable from the concrete state), and each
    alternative returns a single state. By structural induction the whole
    statement list produces a singleton. -/
theorem execStmtsSuccs_singleton
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (ip_reg : Reg) (fallthrough : UInt64)
    (stmts : List (Stmt Reg)) (cfg : ConcreteState Reg × TempEnv) :
    ∃ x, execStmtsSuccs ip_reg fallthrough stmts cfg = {x} := by
  induction stmts generalizing cfg with
  | nil =>
    rcases cfg with ⟨state, _⟩
    by_cases h : fallthrough == (0 : UInt64)
    · exact ⟨state, by simp [execStmtsSuccs, h]⟩
    · exact ⟨state.write ip_reg fallthrough, by simp [execStmtsSuccs, h]⟩
  | cons stmt stmts ih =>
    cases stmt with
    | linear stmt =>
      simpa [execStmtsSuccs] using ih (execLinearStmt cfg stmt)
    | branch stmt =>
      let bridge := branchStmtBridge ip_reg stmt
      by_cases h : bridge.fires cfg = true
      · exact ⟨bridge.taken cfg, by simp [execStmtsSuccs, bridge, h]⟩
      · have hFalse : bridge.fires cfg = false := by
          cases hf : bridge.fires cfg
          · rfl
          · exact absurd hf h
        simpa [execStmtsSuccs, bridge, hFalse] using ih (bridge.cont cfg)

/-- `execBlockSuccs` always returns exactly one concrete successor.

    Follows from `execStmtsSuccs_singleton`: one block, one concrete input,
    one deterministic output. -/
theorem execBlockSuccs_singleton
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (block : Block Reg) (s : ConcreteState Reg) :
    ∃ x, execBlockSuccs block s = {x} :=
  execStmtsSuccs_singleton block.ip_reg block.next block.stmts (s, TempEnv.empty)

/-! ## Dispatch Loop Body Branch Soundness -/

/-- **Branch model soundness for the dispatch loop.**

    Every enabled branch in the single-block path model computes exactly
    `bodyEffect s`.

    The proof requires `hAllBlocks`: for any block `blk ∈ allBlocks`, if any
    summary of `blk` is enabled at `s`, then `bodyEffect s` is in `blk`'s
    concrete successors at `s`.  In the dispatch loop this holds because:
    - summaries of `blk` are only enabled when `rip(s) = blk.ip`
    - `bodyEffect s = execBlock blk_rip s` where `blk_rip` is the block at `rip(s)`
    - so `blk = blk_rip` and `bodyEffect s ∈ execBlockSuccs blk s`

    Note: the task description's proposed hypothesis
    `hStep : ∀ s, ∃ b ∈ allBlocks, bodyEffect s ∈ execBlockSuccs b s`
    is not sufficient by itself: it only says *some* block covers each body step,
    not necessarily the specific block `blk` whose summary fired at `s`.
    `hAllBlocks` is strictly stronger and is needed for soundness.
    (`hStep` is instead what drives `dispatch_bodyPathStepRealizable`.)

    **Proof structure:** extract `τ ∈ lowerBlockSummaries blk` from the branch,
    apply `lowerBlockSummaries_complete` to put `Summary.apply τ s` in
    `execBlockSuccs blk s`, apply `hAllBlocks` to put `bodyEffect s` in the
    same singleton set, conclude they are equal by `execBlockSuccs_singleton`. -/
theorem dispatch_bodyBranchSound
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (loop : VexLoopSummary Reg)
    (allBlocks : Finset (Block Reg))
    (hAllBlocks : ∀ s blk, blk ∈ allBlocks →
        (∃ σ ∈ lowerBlockSummaries blk, Summary.enabled σ s) →
        loop.bodyEffect s ∈ execBlockSuccs blk s) :
    BranchModel.Sound (vexSummaryISA Reg)
      (↑(bodyBranchModel (allBlocks.image (fun b => [b]))) :
        Set (Branch (SymSub Reg) (SymPC Reg)))
      (fun s s' => s' = loop.bodyEffect s) := by
  intro b_br hb_br s hsat
  -- Unpack: b_br = summaryAsBranch σ for σ ∈ lowerPathFamilySummaries of the single-block paths
  have hb_br_fin : b_br ∈ bodyBranchModel (allBlocks.image (fun b => [b])) :=
    Finset.mem_coe.mp hb_br
  -- bodyBranchModel paths = (lowerPathFamilySummaries paths).image summaryAsBranch
  rcases Finset.mem_image.mp hb_br_fin with ⟨σ, hσMem, rfl⟩
  -- σ ∈ lowerPathFamilySummaries (allBlocks.image (fun b => [b]))
  -- = (allBlocks.image (fun b => [b])).biUnion lowerBlockPathSummaries
  -- = allBlocks.biUnion (fun blk => lowerBlockPathSummaries [blk])
  simp only [lowerPathFamilySummaries, Finset.mem_biUnion, Finset.mem_image] at hσMem
  obtain ⟨path, ⟨blk, hblkMem, rfl⟩, hσPath⟩ := hσMem
  -- σ ∈ lowerBlockPathSummaries [blk]
  -- = composeSummaryFinsets (lowerBlockSummaries blk) {Summary.id}
  -- = (lowerBlockSummaries blk).biUnion (fun τ => {Summary.compose τ Summary.id})
  simp only [lowerBlockPathSummaries, composeSummaryFinsets,
    Finset.mem_biUnion, Finset.mem_image, Finset.mem_singleton] at hσPath
  obtain ⟨τ, hτMem, rid, hrid, hτCompose⟩ := hσPath
  -- hrid : rid = Summary.id, hτCompose : τ.compose rid = σ
  subst hrid
  -- σ = Summary.compose τ Summary.id, with τ ∈ lowerBlockSummaries blk
  -- Extract enablement of τ from enablement of σ = Summary.compose τ Summary.id
  -- summaryAsBranch (Summary.compose τ Summary.id) has:
  --   .sub = composeSymSub τ.sub SymSub.id
  --   .pc  = .and τ.pc (substSymPC τ.sub .true)
  rw [← hτCompose] at hsat ⊢
  have hτEnabled : Summary.enabled τ s := by
    simp only [summaryAsBranch, Summary.compose, Summary.id, vexSummaryISA] at hsat
    simp only [Summary.enabled, satisfiesSymPC, evalSymPC, Bool.and_eq_true, substSymPC] at hsat ⊢
    exact hsat.1
  -- Summary.apply τ s ∈ execBlockSuccs blk s  (lowering completeness)
  have hτSucc : Summary.apply τ s ∈ execBlockSuccs blk s :=
    lowerBlockSummaries_complete blk s τ hτMem hτEnabled
  -- loop.bodyEffect s ∈ execBlockSuccs blk s  (dispatch hypothesis)
  have hBodySucc : loop.bodyEffect s ∈ execBlockSuccs blk s :=
    hAllBlocks s blk hblkMem ⟨τ, hτMem, hτEnabled⟩
  -- execBlockSuccs blk s is a singleton {x}: both outputs must agree
  obtain ⟨x, hx⟩ := execBlockSuccs_singleton blk s
  have hτEq : Summary.apply τ s = x := by
    rw [hx] at hτSucc; exact Finset.mem_singleton.mp hτSucc
  have hBodyEq : loop.bodyEffect s = x := by
    rw [hx] at hBodySucc; exact Finset.mem_singleton.mp hBodySucc
  -- Conclude: (vexSummaryISA Reg).eval_sub (summaryAsBranch (τ.compose Summary.id)).sub s
  --         = loop.bodyEffect s
  simp only [summaryAsBranch, Summary.compose, Summary.id, vexSummaryISA]
  rw [composeSymSub_apply, applySymSub_id]
  simp only [Summary.apply] at hτEq
  rw [hτEq, ← hBodyEq]

end VexISA
