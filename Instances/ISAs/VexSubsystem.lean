import Instances.ISAs.VexWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

/-- A finite path-family witness for the fetched-trace behavior of a VEX subsystem. -/
structure FetchedSubsystemWitness
    (Reg : Type) (Obs : Type) [DecidableEq Reg] [Fintype Reg] where
  program : Program Reg
  ip_reg : Reg
  Relevant : ConcreteState Reg → Prop
  observe : ConcreteState Reg → Obs
  paths : Finset (List (Block Reg))
  complete : ∀ s o,
    ExecProgramTraceDenotesObs Relevant observe program ip_reg s o ↔
      ExecPathFamilyDenotesObs Relevant observe paths s o

/-- The extracted path-family summaries of a fetched subsystem witness are an adequate
observation-level model of the fetched subsystem trace semantics. -/
def FetchedSubsystemExtractible
    {Reg : Type} {Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (w : FetchedSubsystemWitness Reg Obs) : Prop :=
  ∀ s o,
    VexModelDenotesObs w.Relevant w.observe (lowerPathFamilySummaries w.paths) s o ↔
      ExecProgramTraceDenotesObs w.Relevant w.observe w.program w.ip_reg s o

/-- Any complete finite fetched-path witness yields an adequate extracted model of the
corresponding fetched subsystem behavior. -/
theorem extractedModel_of_fetchedSubsystemWitness
    {Reg : Type} {Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (w : FetchedSubsystemWitness Reg Obs) :
    FetchedSubsystemExtractible w := by
  intro s o
  exact Iff.trans
    (lowerPathFamilySummaries_denotesObs_iff_execPathFamily w.Relevant w.observe w.paths s o)
    (w.complete s o).symm

/-- Any two complete path-family witnesses for the same fetched subsystem trace semantics
induce observation-equivalent extracted models. -/
theorem completeFetchedWitnesses_modelEq
    {Reg : Type} {Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (program : Program Reg) (ip_reg : Reg)
    (Relevant : ConcreteState Reg → Prop)
    (observe : ConcreteState Reg → Obs)
    (paths₁ paths₂ : Finset (List (Block Reg)))
    (h₁ : ∀ s o,
      ExecProgramTraceDenotesObs Relevant observe program ip_reg s o ↔
        ExecPathFamilyDenotesObs Relevant observe paths₁ s o)
    (h₂ : ∀ s o,
      ExecProgramTraceDenotesObs Relevant observe program ip_reg s o ↔
        ExecPathFamilyDenotesObs Relevant observe paths₂ s o) :
    VexModelEq Relevant observe
      (lowerPathFamilySummaries paths₁)
      (lowerPathFamilySummaries paths₂) := by
  intro s o
  exact Iff.trans
    (Iff.trans
      (lowerPathFamilySummaries_denotesObs_iff_execPathFamily Relevant observe paths₁ s o)
      (h₁ s o).symm)
    (Iff.trans
      (h₂ s o)
      (lowerPathFamilySummaries_denotesObs_iff_execPathFamily Relevant observe paths₂ s o).symm)

end VexISA
