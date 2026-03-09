import Instances.ISAs.VexWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA

namespace Instances.Examples.Phase2Composition

inductive ComposeReg where
  | r0
  | r1
  | r2
  deriving DecidableEq, Repr

instance : Fintype ComposeReg where
  elems := {ComposeReg.r0, ComposeReg.r1, ComposeReg.r2}
  complete := by
    intro r
    cases r <;> simp

abbrev Reg := ComposeReg

noncomputable local instance :
    ∀ (s : ConcreteState Reg) (φ : SymPC Reg),
      Decidable ((vexSummaryISA Reg).satisfies s φ) := by
  intro s φ
  simpa [satisfiesSymPC] using
    (inferInstance : Decidable (evalSymPC s φ = true))

def blockA : Block Reg :=
  { stmts := [Stmt.put .r2 (.add64 (.get .r0) (.const 1))]
    ip_reg := .r1
    next := 1 }


def blockB : Block Reg :=
  { stmts := [Stmt.branch (BranchStmt.exit (Cond.eq64 (.get .r2) (.const 0)) 0x1000)]
    ip_reg := .r1
    next := 2 }


def pathAB : List (Block Reg) := [blockA, blockB]


def blockASummary : Summary Reg :=
  { sub := SymSub.write (SymSub.write SymSub.id .r2 (.add64 (.reg .r0) (.const 1))) .r1 (.const 1)
    pc := .true }


def blockBTakenSummary : Summary Reg :=
  { sub := SymSub.write SymSub.id .r1 (.const 0x1000)
    pc := .and .true (.eq (.reg .r2) (.const 0)) }


def blockBFallSummary : Summary Reg :=
  { sub := SymSub.write SymSub.id .r1 (.const 2)
    pc := .and .true (.not (.eq (.reg .r2) (.const 0))) }


def pathASummary : Summary Reg :=
  Summary.compose blockASummary Summary.id


def pathBTakenSummary : Summary Reg :=
  Summary.compose blockBTakenSummary Summary.id


def pathBFallSummary : Summary Reg :=
  Summary.compose blockBFallSummary Summary.id


def expectedTaken : Summary Reg :=
  Summary.compose pathASummary pathBTakenSummary


def expectedFall : Summary Reg :=
  Summary.compose pathASummary pathBFallSummary


def composedSummaries : Finset (Summary Reg) :=
  composeSummaryFinsets (lowerBlockPathSummaries [blockA]) (lowerBlockPathSummaries [blockB])


def composedBranchModel : Finset (Branch (SymSub Reg) (SymPC Reg)) :=
  composedSummaries.image summaryAsBranch


def closure : Finset (SymPC Reg) := {expectedTaken.pc, expectedFall.pc}


def behavior (s s' : ConcreteState Reg) : Prop :=
  s' ∈ execBlockPath pathAB s

private theorem lowerBlockSummariesA_eq_expected :
    lowerBlockSummaries blockA = {blockASummary} := by
  native_decide

private theorem lowerBlockSummariesB_eq_expected :
    lowerBlockSummaries blockB = {blockBTakenSummary, blockBFallSummary} := by
  native_decide

private theorem lowerBlockPathSummariesA_eq_expected :
    lowerBlockPathSummaries [blockA] = {pathASummary} := by
  native_decide

private theorem lowerBlockPathSummariesB_eq_expected :
    lowerBlockPathSummaries [blockB] = {pathBTakenSummary, pathBFallSummary} := by
  native_decide

private theorem composedSummaries_eq_expected :
    composedSummaries = {expectedTaken, expectedFall} := by
  ext summary
  simp [composedSummaries, lowerBlockPathSummariesA_eq_expected,
    lowerBlockPathSummariesB_eq_expected, expectedTaken, expectedFall, composeSummaryFinsets]

private theorem composed_modelEqState :
    VexModelEqState (fun _ : ConcreteState Reg => True)
      composedSummaries
      (lowerBlockPathSummaries pathAB) := by
  simpa [composedSummaries] using
    (lowerBlockPathSummaries_append_modelEqState (Reg := Reg) (Relevant := fun _ => True) [blockA] [blockB])

example :
    VexModelEqState (fun _ : ConcreteState Reg => True)
      composedSummaries
      (lowerBlockPathSummaries pathAB) :=
  composed_modelEqState

example : composedSummaries = {expectedTaken, expectedFall} :=
  composedSummaries_eq_expected

private theorem h_contains : ∀ b ∈ composedBranchModel, b.pc ∈ closure := by
  intro b hb
  have hb' : b = summaryAsBranch expectedTaken ∨ b = summaryAsBranch expectedFall := by
    simpa [composedBranchModel, composedSummaries_eq_expected] using hb
  rcases hb' with rfl | rfl <;> simp [closure]

private theorem taken_lift_taken :
    substSymPC expectedTaken.sub expectedTaken.pc = expectedTaken.pc := by
  native_decide

private theorem taken_lift_fall :
    substSymPC expectedTaken.sub expectedFall.pc = expectedFall.pc := by
  native_decide

private theorem fall_lift_taken :
    substSymPC expectedFall.sub expectedTaken.pc = expectedTaken.pc := by
  native_decide

private theorem fall_lift_fall :
    substSymPC expectedFall.sub expectedFall.pc = expectedFall.pc := by
  native_decide

private theorem h_semClosed :
    SemClosed (vexSummaryISA Reg) composedBranchModel closure := by
  intro b hb φ hφ s₁ s₂ hEq
  have hb' : b = summaryAsBranch expectedTaken ∨ b = summaryAsBranch expectedFall := by
    simpa [composedBranchModel, composedSummaries_eq_expected] using hb
  have hφ' : φ = expectedTaken.pc ∨ φ = expectedFall.pc := by
    simpa [closure] using hφ
  rcases hb' with rfl | rfl
  · rcases hφ' with rfl | rfl
    · simpa [vexSummaryISA, satisfiesSymPC, taken_lift_taken] using
        hEq expectedTaken.pc (by simp [closure])
    · simpa [vexSummaryISA, satisfiesSymPC, taken_lift_fall] using
        hEq expectedFall.pc (by simp [closure])
  · rcases hφ' with rfl | rfl
    · simpa [vexSummaryISA, satisfiesSymPC, fall_lift_taken] using
        hEq expectedTaken.pc (by simp [closure])
    · simpa [vexSummaryISA, satisfiesSymPC, fall_lift_fall] using
        hEq expectedFall.pc (by simp [closure])

private theorem h_sound :
    BranchModel.Sound (vexSummaryISA Reg)
      (↑composedBranchModel : Set (Branch (SymSub Reg) (SymPC Reg)))
      behavior := by
  intro b hb s hsat
  have hb' : b ∈ composedSummaries.image summaryAsBranch := by
    simpa [composedBranchModel] using hb
  rcases Finset.mem_image.mp hb' with ⟨summary, hSummary, rfl⟩
  have hMem : Summary.apply summary s ∈ summarySuccs composedSummaries s := by
    exact (mem_summarySuccs composedSummaries s (Summary.apply summary s)).2
      ⟨summary, hSummary, hsat, rfl⟩
  simpa [behavior, composedSummaries, summaryAsBranch, vexSummaryISA,
    summarySuccs_composeLowerBlockPathSummaries_eq_execBlockPath_append [blockA] [blockB] s] using hMem

private theorem h_complete :
    BranchModel.Complete (vexSummaryISA Reg)
      (↑composedBranchModel : Set (Branch (SymSub Reg) (SymPC Reg)))
      behavior := by
  intro s s' hs'
  have hMem : s' ∈ summarySuccs composedSummaries s := by
    simpa [behavior, composedSummaries,
      summarySuccs_composeLowerBlockPathSummaries_eq_execBlockPath_append [blockA] [blockB] s] using hs'
  rcases (mem_summarySuccs composedSummaries s s').1 hMem with
    ⟨summary, hSummary, hEnabled, hApply⟩
  refine ⟨summaryAsBranch summary, ?_, hEnabled, ?_⟩
  · exact Finset.mem_coe.mpr <| by
      simpa [composedBranchModel] using (Finset.mem_image.mpr ⟨summary, hSummary, rfl⟩)
  · simpa [summaryAsBranch, vexSummaryISA] using hApply

example :
    CrossBisimulation
      (Quotient.mk (pcSetoidWith (vexSummaryISA Reg) closure))
      behavior
      (abstractBehaviorWith (vexSummaryISA Reg) composedBranchModel closure) := by
  exact quotient_bisimulationSem (vexSummaryISA Reg)
    composedBranchModel closure h_contains h_semClosed behavior h_sound h_complete

end Instances.Examples.Phase2Composition
