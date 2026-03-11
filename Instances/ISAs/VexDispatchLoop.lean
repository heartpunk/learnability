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

## The One New Proof

Everything in the convergence chain — `BranchClassesStable` →
`whileBranchingLoopWitnessComplete_of_branchClassesStable` →
`extractedModel_of_witnessComplete` — is already proved in the framework.

The only new proof needed is `dispatch_bodyPathStepRealizable`:
for every concrete state `s`, the block at `rip(s)` constitutes a valid
body-path representative for `bodyEffect s`. This connects "we have all
the blocks" to "the dispatch loop machinery applies."

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

    This is the ONLY new proof needed for the full interprocedural
    grammar extraction pipeline for mutually recursive CFG parsers.
    All other pieces (`BranchClassesStable` → orbit cycling →
    `whileBranchingLoopWitnessComplete` → `extractedModel`) are already
    proved in the framework. -/
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

end VexISA
