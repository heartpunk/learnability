import Mathlib.Data.Fintype.Basic
import ModelEq
import Instances.ISAs.VexProgram

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

abbrev VexModelDenotesObs {Reg : Type} {Obs : Type*} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop) (observe : ConcreteState Reg → Obs)
    (M : Finset (Summary Reg)) (s : ConcreteState Reg) (o : Obs) : Prop :=
  ModelDenotesObs Summary.enabled Summary.apply Relevant observe M s o

abbrev VexSummaryEq {Reg : Type} {Obs : Type*} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop) (observe : ConcreteState Reg → Obs)
    (a b : Summary Reg) : Prop :=
  SummaryEq Summary.enabled Summary.apply Relevant observe a b

abbrev VexModelEq {Reg : Type} {Obs : Type*} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop) (observe : ConcreteState Reg → Obs)
    (M N : Finset (Summary Reg)) : Prop :=
  ModelEq Summary.enabled Summary.apply Relevant observe M N

abbrev VexModelEqState {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop)
    (M N : Finset (Summary Reg)) : Prop :=
  ModelEqState Summary.enabled Summary.apply Relevant M N

/-- Observation-level denotation of a raw VEX block through its concrete successor set. -/
def ExecBlockDenotesObs {Reg : Type} {Obs : Type*} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop) (observe : ConcreteState Reg → Obs)
    (block : Block Reg) (s : ConcreteState Reg) (o : Obs) : Prop :=
  Relevant s ∧ ∃ s' ∈ execBlockSuccs block s, observe s' = o

/-- Observation-level denotation of a fixed VEX block path through its concrete successor set. -/
def ExecBlockPathDenotesObs {Reg : Type} {Obs : Type*} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop) (observe : ConcreteState Reg → Obs)
    (blocks : List (Block Reg)) (s : ConcreteState Reg) (o : Obs) : Prop :=
  Relevant s ∧ ∃ s' ∈ execBlockPath blocks s, observe s' = o

/-- Observation-level denotation of a summary family through its executable successor set. -/
def SummarySuccsDenotesObs {Reg : Type} {Obs : Type*} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop) (observe : ConcreteState Reg → Obs)
    (summaries : Finset (Summary Reg)) (s : ConcreteState Reg) (o : Obs) : Prop :=
  Relevant s ∧ ∃ s' ∈ summarySuccs summaries s, observe s' = o

theorem vexModelDenotesObs_iff_summarySuccsDenotesObs
    {Reg : Type} {Obs : Type*} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop) (observe : ConcreteState Reg → Obs)
    (summaries : Finset (Summary Reg)) (s : ConcreteState Reg) (o : Obs) :
    VexModelDenotesObs Relevant observe summaries s o ↔
      SummarySuccsDenotesObs Relevant observe summaries s o := by
  constructor
  · intro h
    rcases h with ⟨hRel, summary, hMem, hEnabled, hObs⟩
    refine ⟨hRel, Summary.apply summary s, ?_, hObs⟩
    exact (mem_summarySuccs summaries s (Summary.apply summary s)).2 ⟨summary, hMem, hEnabled, rfl⟩
  · intro h
    rcases h with ⟨hRel, s', hMem, hObs⟩
    rcases (mem_summarySuccs summaries s s').1 hMem with ⟨summary, hSummary, hEnabled, hApply⟩
    exact ⟨hRel, summary, hSummary, hEnabled, by simpa [hApply] using hObs⟩

theorem lowerBlockSummaries_denotesObs_iff_execBlock
    {Reg : Type} {Obs : Type*} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop) (observe : ConcreteState Reg → Obs)
    (block : Block Reg) (s : ConcreteState Reg) (o : Obs) :
    VexModelDenotesObs Relevant observe (lowerBlockSummaries block) s o ↔
      ExecBlockDenotesObs Relevant observe block s o := by
  rw [vexModelDenotesObs_iff_summarySuccsDenotesObs]
  constructor
  · rintro ⟨hRel, s', hMem, hObs⟩
    exact ⟨hRel, s', by simpa [summarySuccs_lowerBlockSummaries_eq_execBlockSuccs block s] using hMem, hObs⟩
  · rintro ⟨hRel, s', hMem, hObs⟩
    exact ⟨hRel, s', by simpa [summarySuccs_lowerBlockSummaries_eq_execBlockSuccs block s] using hMem, hObs⟩

theorem lowerBlockPathSummaries_denotesObs_iff_execBlockPath
    {Reg : Type} {Obs : Type*} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop) (observe : ConcreteState Reg → Obs)
    (blocks : List (Block Reg)) (s : ConcreteState Reg) (o : Obs) :
    VexModelDenotesObs Relevant observe (lowerBlockPathSummaries blocks) s o ↔
      ExecBlockPathDenotesObs Relevant observe blocks s o := by
  rw [vexModelDenotesObs_iff_summarySuccsDenotesObs]
  constructor
  · rintro ⟨hRel, s', hMem, hObs⟩
    exact ⟨hRel, s', by simpa [summarySuccs_lowerBlockPathSummaries_eq_execBlockPath blocks s] using hMem, hObs⟩
  · rintro ⟨hRel, s', hMem, hObs⟩
    exact ⟨hRel, s', by simpa [summarySuccs_lowerBlockPathSummaries_eq_execBlockPath blocks s] using hMem, hObs⟩

end VexISA
