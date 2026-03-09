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

/-- Concrete fetched-subsystem behavior as a state-to-state relation. -/
def FetchedSubsystemBehavior
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (program : Program Reg) (ip_reg : Reg)
    (Relevant : ConcreteState Reg → Prop)
    (s s' : ConcreteState Reg) : Prop :=
  Relevant s ∧ Relation.ReflTransGen (ProgramStep program ip_reg) s s'

/-- Branch model induced by flattening the witness path-family summaries. -/
def fetchedSubsystemBranchModel
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (paths : Finset (List (Block Reg))) :
    Finset (Branch (SymSub Reg) (SymPC Reg)) :=
  (lowerPathFamilySummaries paths).image summaryAsBranch

/-- A fetched subsystem witness with identity observation gives completeness of the
    induced branch model for the fetched trace behavior. -/
theorem fetchedSubsystem_branchComplete
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    [∀ (s : ConcreteState Reg) (φ : SymPC Reg),
      Decidable ((vexSummaryISA Reg).satisfies s φ)]
    (w : FetchedSubsystemWitness Reg (ConcreteState Reg))
    (h_observe : w.observe = fun state => state) :
    BranchModel.Complete (vexSummaryISA Reg)
      (↑(fetchedSubsystemBranchModel w.paths) : Set (Branch (SymSub Reg) (SymPC Reg)))
      (FetchedSubsystemBehavior w.program w.ip_reg w.Relevant) := by
  intro s s' hs'
  have hProgObs : ExecProgramTraceDenotesObs w.Relevant (fun state => state) w.program w.ip_reg s s' :=
    ⟨hs'.1, s', hs'.2, rfl⟩
  have hcomplete :
      ExecProgramTraceDenotesObs w.Relevant (fun state => state) w.program w.ip_reg s s' ↔
        ExecPathFamilyDenotesObs w.Relevant (fun state => state) w.paths s s' := by
    simpa [h_observe] using (w.complete s s')
  have hPathObs : ExecPathFamilyDenotesObs w.Relevant (fun state => state) w.paths s s' :=
    hcomplete.mp hProgObs
  have hModelObs :
      VexModelDenotesObs w.Relevant (fun state => state) (lowerPathFamilySummaries w.paths) s s' :=
    (lowerPathFamilySummaries_denotesObs_iff_execPathFamily w.Relevant (fun state => state) w.paths s s').mpr hPathObs
  rcases hModelObs with ⟨_, summary, hSummary, hEnabled, hApply⟩
  refine ⟨summaryAsBranch summary, ?_, hEnabled, ?_⟩
  · exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨summary, hSummary, rfl⟩)
  · simpa [FetchedSubsystemBehavior, summaryAsBranch, vexSummaryISA] using hApply

/-- A fetched subsystem witness with identity observation gives soundness of the
    induced branch model for the fetched trace behavior. -/
theorem fetchedSubsystem_branchSound
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    [∀ (s : ConcreteState Reg) (φ : SymPC Reg),
      Decidable ((vexSummaryISA Reg).satisfies s φ)]
    (w : FetchedSubsystemWitness Reg (ConcreteState Reg))
    (h_observe : w.observe = fun state => state) :
    (∀ s, ∀ summary ∈ lowerPathFamilySummaries w.paths,
      Summary.enabled summary s → w.Relevant s) →
    BranchModel.Sound (vexSummaryISA Reg)
      (↑(fetchedSubsystemBranchModel w.paths) : Set (Branch (SymSub Reg) (SymPC Reg)))
      (FetchedSubsystemBehavior w.program w.ip_reg w.Relevant) := by
  intro h_relevant b hb s hsat
  rcases Finset.mem_image.mp (Finset.mem_coe.mp hb) with ⟨summary, hSummary, rfl⟩
  have hRel : w.Relevant s := h_relevant s summary hSummary hsat
  have hModelObs :
      VexModelDenotesObs w.Relevant (fun state => state)
        (lowerPathFamilySummaries w.paths) s (Summary.apply summary s) :=
    ⟨hRel, summary, hSummary, hsat, rfl⟩
  have hPathObs :
      ExecPathFamilyDenotesObs w.Relevant (fun state => state)
        w.paths s (Summary.apply summary s) :=
    (lowerPathFamilySummaries_denotesObs_iff_execPathFamily
      w.Relevant (fun state => state) w.paths s (Summary.apply summary s)).mp hModelObs
  have hcomplete :
      ExecProgramTraceDenotesObs w.Relevant (fun state => state)
          w.program w.ip_reg s (Summary.apply summary s) ↔
        ExecPathFamilyDenotesObs w.Relevant (fun state => state)
          w.paths s (Summary.apply summary s) := by
    simpa [h_observe] using (w.complete s (Summary.apply summary s))
  have hProgObs :
      ExecProgramTraceDenotesObs w.Relevant (fun state => state)
        w.program w.ip_reg s (Summary.apply summary s) :=
    hcomplete.mpr hPathObs
  rcases hProgObs with ⟨hRel', _, hTrace, rfl⟩
  exact ⟨hRel', hTrace⟩

/-- A fetched subsystem witness with identity observation yields a semantic-closure
    STS1-style quotient for its flattened witness-path branch model, provided
    summaries only fire on relevant inputs. -/
theorem fetchedSubsystemRefinementBisimulation
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    [∀ (s : ConcreteState Reg) (φ : SymPC Reg),
      Decidable ((vexSummaryISA Reg).satisfies s φ)]
    (w : FetchedSubsystemWitness Reg (ConcreteState Reg))
    (h_observe : w.observe = fun state => state)
    (closure : Finset (SymPC Reg))
    (h_contains : ∀ b ∈ fetchedSubsystemBranchModel w.paths, b.pc ∈ closure)
    (h_semClosed : SemClosed (vexSummaryISA Reg) (fetchedSubsystemBranchModel w.paths) closure)
    (h_relevant : ∀ s, ∀ summary ∈ lowerPathFamilySummaries w.paths,
      Summary.enabled summary s → w.Relevant s) :
    CrossBisimulation
      (Quotient.mk (pcSetoidWith (vexSummaryISA Reg) closure))
    (FetchedSubsystemBehavior w.program w.ip_reg w.Relevant)
      (abstractBehaviorWith (vexSummaryISA Reg) (fetchedSubsystemBranchModel w.paths) closure) := by
  exact quotient_bisimulationSem (vexSummaryISA Reg)
    (fetchedSubsystemBranchModel w.paths) closure
    h_contains h_semClosed
    (FetchedSubsystemBehavior w.program w.ip_reg w.Relevant)
    (fetchedSubsystem_branchSound w h_observe h_relevant)
    (fetchedSubsystem_branchComplete w h_observe)

/-- The semantic-closure fetched-subsystem quotient has at most `2^|closure|`
    abstract states. -/
theorem fetchedSubsystemRefinement_card_bound
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    [∀ (s : ConcreteState Reg) (φ : SymPC Reg),
      Decidable ((vexSummaryISA Reg).satisfies s φ)]
    (closure : Finset (SymPC Reg)) :
    Fintype.card (Quotient (pcSetoidWith (vexSummaryISA Reg) closure)) ≤
      2 ^ closure.card := by
  exact abstractStateWith_card_bound (vexSummaryISA Reg) closure

end VexISA
