import Instances.ISAs.VexWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA

namespace Instances.Examples.Phase3Combinatorial

inductive BranchReg where
  | r0
  | r1
  | r2
  deriving DecidableEq, Repr

instance : Fintype BranchReg where
  elems := {BranchReg.r0, BranchReg.r1, BranchReg.r2}
  complete := by
    intro r
    cases r <;> simp

abbrev Reg := BranchReg

noncomputable local instance :
    ∀ (s : ConcreteState Reg) (φ : SymPC Reg),
      Decidable ((vexSummaryISA Reg).satisfies s φ) := by
  intro s φ
  simpa [satisfiesSymPC] using
    (inferInstance : Decidable (evalSymPC s φ = true))

def blockA : Block Reg :=
  { stmts := [Stmt.branch (BranchStmt.exit (Cond.eq64 (.get .r0) (.const 0)) 0x10)]
    ip_reg := .r1
    next := 0x20 }


def blockB : Block Reg :=
  { stmts := [Stmt.put .r2 (.const 0), Stmt.put .r1 (.const 0)]
    ip_reg := .r1
    next := 0 }


def blockC : Block Reg :=
  { stmts := [Stmt.put .r2 (.const 1), Stmt.put .r1 (.const 0)]
    ip_reg := .r1
    next := 0 }


def pathLeft : List (Block Reg) := [blockA, blockB]
def pathRight : List (Block Reg) := [blockA, blockC]

def bodyPaths : Finset (List (Block Reg)) := {pathLeft, pathRight}

def observe (s : ConcreteState Reg) : UInt64 × UInt64 :=
  (s.read .r1, s.read .r2)

example :
    ExtractiblePathFamilyModel (Reg := Reg) (Relevant := fun _ : ConcreteState Reg => True) (Obs := UInt64 × UInt64)
      observe bodyPaths := by
  exact lowerPathFamilySummaries_denotesObs_iff_execPathFamily (Reg := Reg) (Relevant := fun _ => True) (observe := observe) bodyPaths


def blockATakenSummary : Summary Reg :=
  { sub := SymSub.write SymSub.id .r1 (.const 0x10), pc := .and .true (.eq (.reg .r0) (.const 0)) }


def blockAFallSummary : Summary Reg :=
  { sub := SymSub.write SymSub.id .r1 (.const 0x20), pc := .and .true (.not (.eq (.reg .r0) (.const 0))) }


def pathBSummary : Summary Reg :=
  Summary.compose
    { sub := SymSub.write (SymSub.write SymSub.id .r2 (.const 0)) .r1 (.const 0), pc := .true }
    Summary.id


def pathCSummary : Summary Reg :=
  Summary.compose
    { sub := SymSub.write (SymSub.write SymSub.id .r2 (.const 1)) .r1 (.const 0), pc := .true }
    Summary.id


def expectedLeft : Summary Reg :=
  Summary.compose blockATakenSummary pathBSummary


def expectedRight : Summary Reg :=
  Summary.compose blockAFallSummary pathCSummary


def closure : Finset (SymPC Reg) := {expectedLeft.pc, expectedRight.pc}

private theorem expectedLeft_mem :
    expectedLeft ∈ lowerBlockPathSummaries pathLeft := by
  native_decide

private theorem expectedRight_mem :
    expectedRight ∈ lowerBlockPathSummaries pathRight := by
  native_decide

private theorem sZero_left :
    let s : ConcreteState Reg :=
      { regs := fun
          | .r0 => 0
          | .r1 => 0
          | .r2 => 99
        mem := ∅ }
    ∃ cls : LiveBranchClass Reg, cls.path = pathLeft ∧ cls.Realizes bodyPaths closure s := by
  dsimp
  let s : ConcreteState Reg :=
      { regs := fun
          | .r0 => 0
          | .r1 => 0
          | .r2 => 99
        mem := ∅ }
  let cls : LiveBranchClass Reg :=
    { path := pathLeft
      summary := expectedLeft
      signature := pcSignatureWith (vexSummaryISA Reg) closure s }
  refine ⟨cls, rfl, ?_⟩
  change cls.Realizes bodyPaths closure s
  unfold LiveBranchClass.Realizes
  dsimp [cls]
  refine ⟨by simp [bodyPaths], expectedLeft_mem, ?_, rfl⟩
  have hA : Summary.enabled blockATakenSummary s := by
    change evalSymPC s (.and .true (.eq (.reg .r0) (.const 0))) = true
    native_decide
  have hB : Summary.enabled pathBSummary (Summary.apply blockATakenSummary s) := by
    change
      evalSymPC (Summary.apply blockATakenSummary s)
        (.and .true (substSymPC
          (SymSub.write (SymSub.write SymSub.id BranchReg.r2 (.const 0)) BranchReg.r1 (.const 0))
          .true)) = true
    native_decide
  exact (Summary.compose_enabled_iff blockATakenSummary pathBSummary s).2 ⟨hA, hB⟩

private theorem sOne_right :
    let s : ConcreteState Reg :=
      { regs := fun
          | .r0 => 1
          | .r1 => 0
          | .r2 => 99
        mem := ∅ }
    ∃ cls : LiveBranchClass Reg, cls.path = pathRight ∧ cls.Realizes bodyPaths closure s := by
  dsimp
  let s : ConcreteState Reg :=
      { regs := fun
          | .r0 => 1
          | .r1 => 0
          | .r2 => 99
        mem := ∅ }
  let cls : LiveBranchClass Reg :=
    { path := pathRight
      summary := expectedRight
      signature := pcSignatureWith (vexSummaryISA Reg) closure s }
  refine ⟨cls, rfl, ?_⟩
  change cls.Realizes bodyPaths closure s
  unfold LiveBranchClass.Realizes
  dsimp [cls]
  refine ⟨by simp [bodyPaths], expectedRight_mem, ?_, rfl⟩
  have hA : Summary.enabled blockAFallSummary s := by
    change evalSymPC s (.and .true (.not (.eq (.reg .r0) (.const 0)))) = true
    native_decide
  have hC : Summary.enabled pathCSummary (Summary.apply blockAFallSummary s) := by
    change
      evalSymPC (Summary.apply blockAFallSummary s)
        (.and .true (substSymPC
          (SymSub.write (SymSub.write SymSub.id BranchReg.r2 (.const 1)) BranchReg.r1 (.const 0))
          .true)) = true
    native_decide
  exact (Summary.compose_enabled_iff blockAFallSummary pathCSummary s).2 ⟨hA, hC⟩

example :
    let s : ConcreteState Reg :=
      { regs := fun
          | .r0 => 0
          | .r1 => 0
          | .r2 => 99
        mem := ∅ }
    ∃ cls : LiveBranchClass Reg, cls.path = pathLeft ∧ cls.Realizes bodyPaths closure s :=
  sZero_left

example :
    let s : ConcreteState Reg :=
      { regs := fun
          | .r0 => 1
          | .r1 => 0
          | .r2 => 99
        mem := ∅ }
    ∃ cls : LiveBranchClass Reg, cls.path = pathRight ∧ cls.Realizes bodyPaths closure s :=
  sOne_right

end Instances.Examples.Phase3Combinatorial
