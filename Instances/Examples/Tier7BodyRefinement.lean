import Instances.Examples.Tier0Increment
import Instances.ISAs.VexWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA

namespace Instances.Examples.Tier7BodyRefinement

abbrev Reg := Instances.Examples.ToyReg
abbrev block : Block Reg := Instances.Examples.block
abbrev expectedSummary : Summary Reg := Instances.Examples.expectedSummary
abbrev expectedPathSummary : Summary Reg := Instances.Examples.expectedPathSummary

noncomputable local instance :
    ∀ (s : ConcreteState Reg) (φ : SymPC Reg),
      Decidable ((vexSummaryISA Reg).satisfies s φ) := by
  intro s φ
  simpa [satisfiesSymPC] using
    (inferInstance : Decidable (evalSymPC s φ = true))

def bodyPaths : Finset (List (Block Reg)) := {[block]}

def closure : Finset (SymPC Reg) := {expectedPathSummary.pc}

def loop : VexLoopSummary Reg where
  body := CompTree.assign (lowerBlockSub block)
  continues := .not .true
  exits := .true
  bodyEffect := execBlock block
  bodyEffect_spec := by
    intro s s'
    simpa [CompTree.treeBehavior, assignBehavior] using
      (show (s' = applySymSub (lowerBlockSub block) s) ↔ s' = execBlock block s by
        rw [lowerBlockSub_sound block s])
  guard_partition := by
    intro s
    simp [vexSummaryISA, satisfiesSymPC, evalSymPC]

private theorem lowerBlockPathSummaries_eq_expected :
    lowerBlockPathSummaries [block] = {expectedPathSummary} := by
  native_decide

private theorem bodyBranchModel_eq_expected :
    bodyBranchModel bodyPaths = {summaryAsBranch expectedPathSummary} := by
  simp [bodyPaths, bodyBranchModel, lowerPathFamilySummaries, lowerBlockPathSummaries_eq_expected]

private theorem expectedPathSummary_pc :
    expectedPathSummary.pc = SymPC.and SymPC.true SymPC.true := by
  native_decide

private theorem expectedPathSummary_apply (s : ConcreteState Reg) :
    Summary.apply expectedPathSummary s = execBlock block s := by
  have hLower : expectedSummary = lowerBlock block := by
    native_decide
  have hPath : expectedPathSummary = Summary.compose expectedSummary Summary.id := by
    rfl
  calc
    Summary.apply expectedPathSummary s
        = Summary.apply Summary.id (Summary.apply expectedSummary s) := by
            simp [hPath]
    _ = Summary.apply expectedSummary s := by simp
    _ = execBlock block s := by
          simpa [hLower, Summary.apply] using (lowerBlock_sound block s)

private theorem h_contains : ∀ b ∈ bodyBranchModel bodyPaths, b.pc ∈ closure := by
  intro b hb
  have hb' : b = summaryAsBranch expectedPathSummary := by
    simp [bodyBranchModel_eq_expected] at hb
    exact hb
  subst hb'
  simp [closure]

private theorem h_semClosed :
    SemClosed (vexSummaryISA Reg) (bodyBranchModel bodyPaths) closure := by
  intro b hb φ hφ s₁ s₂ _hEq
  have hb' : b = summaryAsBranch expectedPathSummary := by
    simpa [bodyBranchModel_eq_expected] using hb
  have hφ' : φ = expectedPathSummary.pc := by
    simpa [closure] using hφ
  subst hb'
  subst hφ'
  have hlift : substSymPC expectedPathSummary.sub expectedPathSummary.pc = expectedPathSummary.pc := by
    native_decide
  simpa [vexSummaryISA, satisfiesSymPC, hlift] using
    _hEq expectedPathSummary.pc (by simp [closure])

private theorem hstep : BodyPathStepRealizable loop bodyPaths closure := by
  intro s
  let cls : LiveBranchClass Reg :=
    { path := [block]
      summary := expectedPathSummary
      signature := pcSignatureWith (vexSummaryISA Reg) closure s }
  refine ⟨cls, ?_⟩
  change cls.RealizesBodyStep loop bodyPaths closure s
  unfold LiveBranchClass.RealizesBodyStep LiveBranchClass.Realizes
  dsimp [cls]
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨by simp [bodyPaths], ?_, ?_, rfl⟩
    · simp [lowerBlockPathSummaries_eq_expected]
    · simp [Summary.enabled, satisfiesSymPC, expectedPathSummary_pc]
  · simpa [loop] using expectedPathSummary_apply s
  · have hEnabled : Summary.enabled expectedPathSummary s := by
      simp [Summary.enabled, satisfiesSymPC, expectedPathSummary_pc]
    have hMemSucc :
        Summary.apply expectedPathSummary s ∈ summarySuccs (lowerBlockPathSummaries [block]) s := by
      exact (mem_summarySuccs (lowerBlockPathSummaries [block]) s (Summary.apply expectedPathSummary s)).2
        ⟨expectedPathSummary, by simp [lowerBlockPathSummaries_eq_expected], hEnabled, rfl⟩
    have happly : Summary.apply expectedPathSummary s = loop.bodyEffect s := by
      simpa [loop] using expectedPathSummary_apply s
    simpa [summarySuccs_lowerBlockPathSummaries_eq_execBlockPath [block] s, happly] using hMemSucc

private theorem h_sound :
    BranchModel.Sound (vexSummaryISA Reg)
      (↑(bodyBranchModel bodyPaths) : Set (Branch (SymSub Reg) (SymPC Reg)))
      (fun s s' => s' = loop.bodyEffect s) := by
  intro b hb s _hsat
  rcases Finset.mem_image.mp
      (by simpa [bodyPaths, bodyBranchModel, lowerPathFamilySummaries] using hb) with
    ⟨summary, hSummary, rfl⟩
  have hSummary' : summary = expectedPathSummary := by
    simpa [lowerBlockPathSummaries_eq_expected] using hSummary
  subst hSummary'
  simpa [summaryAsBranch, vexSummaryISA, loop, Summary.apply] using expectedPathSummary_apply s

example : BodyDeterministic loop :=
  bodyDeterministic_of_bodyEffect_spec loop

example :
    CrossBisimulation
      (Quotient.mk (pcSetoidWith (vexSummaryISA Reg) closure))
      (fun s s' => s' = loop.bodyEffect s)
      (abstractBehaviorWith (vexSummaryISA Reg) (bodyBranchModel bodyPaths) closure) := by
  exact vexBodyRefinementBisimulation loop bodyPaths closure h_contains h_semClosed hstep h_sound

noncomputable example :
    Fintype.card (Quotient (pcSetoidWith (vexSummaryISA Reg) closure)) ≤ 2 ^ closure.card := by
  exact vexBodyRefinement_card_bound (Reg := Reg) closure

end Instances.Examples.Tier7BodyRefinement
