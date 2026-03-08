import Mathlib.Data.Finset.Union
import Instances.ISAs.VexLoweringCorrectness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

/-- Concrete successor relation induced directly by raw VEX syntax. -/
def SyntaxDenotes (block : Block) (input output : ConcreteState) : Prop :=
  output ∈ execBlockSuccs block input

/-- Concrete successor relation induced by a family of symbolic summaries. -/
def SummaryDenotes (summaries : Finset Summary) (input output : ConcreteState) : Prop :=
  ∃ summary ∈ summaries,
    Summary.enabled summary input ∧ Summary.apply summary input = output

/-- Concrete successor relation induced by lowering a raw VEX block to summaries. -/
def LoweredDenotes (block : Block) (input output : ConcreteState) : Prop :=
  SummaryDenotes (lowerBlockSummaries block) input output

/-- Materialize the concrete successors described by a family of summaries on a fixed input. -/
def summarySuccs (summaries : Finset Summary) (input : ConcreteState) : Finset ConcreteState :=
  Finset.biUnion summaries fun summary =>
    if evalSymPC input summary.pc then ({Summary.apply summary input} : Finset ConcreteState) else ∅

@[simp] theorem syntaxDenotes_iff (block : Block) (input output : ConcreteState) :
    SyntaxDenotes block input output ↔ output ∈ execBlockSuccs block input := by
  rfl

@[simp] theorem summaryDenotes_iff (summaries : Finset Summary) (input output : ConcreteState) :
    SummaryDenotes summaries input output ↔
      ∃ summary ∈ summaries,
        Summary.enabled summary input ∧ Summary.apply summary input = output := by
  rfl

@[simp] theorem loweredDenotes_iff (block : Block) (input output : ConcreteState) :
    LoweredDenotes block input output ↔
      ∃ summary ∈ lowerBlockSummaries block,
        Summary.enabled summary input ∧ Summary.apply summary input = output := by
  rfl

@[simp] theorem mem_summarySuccs (summaries : Finset Summary) (input output : ConcreteState) :
    output ∈ summarySuccs summaries input ↔ SummaryDenotes summaries input output := by
  constructor
  · intro h
    rcases (Finset.mem_biUnion.mp h) with ⟨summary, hMem, hOut⟩
    by_cases hEnabled : evalSymPC input summary.pc = true
    · refine ⟨summary, hMem, ?_, ?_⟩
      · exact hEnabled
      · simp [hEnabled] at hOut
        exact hOut.symm
    · simp [hEnabled] at hOut
  · intro h
    rcases h with ⟨summary, hMem, hEnabled, hApply⟩
    refine Finset.mem_biUnion.mpr ?_
    refine ⟨summary, hMem, ?_⟩
    have hEnabled' : evalSymPC input summary.pc = true := hEnabled
    simp [hEnabled', hApply]

/-- Raw VEX execution is sound with respect to lowered summary denotation. -/
theorem syntax_to_lowered_sound (block : Block) (input output : ConcreteState)
    (hSyntax : SyntaxDenotes block input output) :
    LoweredDenotes block input output := by
  exact lowerBlockSummaries_sound block input output hSyntax

/-- Lowered summary denotation is complete with respect to raw VEX execution. -/
theorem lowered_to_syntax_complete (block : Block) (input output : ConcreteState)
    (hLowered : LoweredDenotes block input output) :
    SyntaxDenotes block input output := by
  rcases hLowered with ⟨summary, hMem, hEnabled, hApply⟩
  simpa [SyntaxDenotes, hApply] using lowerBlockSummaries_complete block input summary hMem hEnabled

/-- The raw-syntax and lowered-summary views induce the same concrete successor relation. -/
theorem syntax_iff_lowered (block : Block) (input output : ConcreteState) :
    SyntaxDenotes block input output ↔ LoweredDenotes block input output := by
  constructor
  · exact syntax_to_lowered_sound block input output
  · exact lowered_to_syntax_complete block input output

/-- Executable set-level form of the commuting triangle for the current VEX slice. -/
theorem summarySuccs_lowerBlockSummaries_eq_execBlockSuccs (block : Block) (input : ConcreteState) :
    summarySuccs (lowerBlockSummaries block) input = execBlockSuccs block input := by
  ext output
  rw [mem_summarySuccs]
  exact (syntax_iff_lowered block input output).symm

end VexISA
