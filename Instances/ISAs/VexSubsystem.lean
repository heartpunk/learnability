import Instances.ISAs.VexWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

/-- A fetched path witness carries both the block sequence and the entry-side path
condition under which that sequence is a valid subsystem trace candidate. -/
structure PathWitness (Reg : Type) [DecidableEq Reg] [Fintype Reg] where
  entryPc : SymPC Reg
  blocks : List (Block Reg)

instance {Reg : Type} [DecidableEq Reg] [Fintype Reg] : DecidableEq (PathWitness Reg) := by
  intro pw₁ pw₂
  by_cases hPc : pw₁.entryPc = pw₂.entryPc
  · by_cases hBlocks : pw₁.blocks = pw₂.blocks
    · cases pw₁
      cases pw₂
      cases hPc
      cases hBlocks
      exact isTrue rfl
    · exact isFalse (fun h => hBlocks (congrArg PathWitness.blocks h))
  · exact isFalse (fun h => hPc (congrArg PathWitness.entryPc h))

/-- Guard a lowered summary by the entry-side path condition of its witness. -/
def guardSummary
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (entryPc : SymPC Reg) (summary : Summary Reg) : Summary Reg :=
  { sub := summary.sub
    pc := SymPC.and entryPc summary.pc }

@[simp] theorem guardSummary_apply
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (entryPc : SymPC Reg) (summary : Summary Reg) (s : ConcreteState Reg) :
    Summary.apply (guardSummary entryPc summary) s = Summary.apply summary s := by
  rfl

@[simp] theorem guardSummary_enabled_iff
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (entryPc : SymPC Reg) (summary : Summary Reg) (s : ConcreteState Reg) :
    Summary.enabled (guardSummary entryPc summary) s ↔
      satisfiesSymPC s entryPc ∧ Summary.enabled summary s := by
  simp [guardSummary, Summary.enabled, satisfiesSymPC]

/-- Lower one path witness by lowering the underlying path and conjoining the witness
entry PC onto every lowered summary. -/
def lowerPathWitnessSummaries
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (pw : PathWitness Reg) : Finset (Summary Reg) :=
  (lowerBlockPathSummaries pw.blocks).image (guardSummary pw.entryPc)

/-- Flatten a finite family of path witnesses into one guarded summary family. -/
def lowerPathWitnessFamilySummaries
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (paths : Finset (PathWitness Reg)) : Finset (Summary Reg) :=
  paths.biUnion lowerPathWitnessSummaries

/-- Concrete observation-level denotation of one path witness. The entry PC must hold
on the initial state before the path is considered valid. -/
def ExecPathWitnessDenotesObs
    {Reg : Type} {Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop)
    (observe : ConcreteState Reg → Obs)
    (pw : PathWitness Reg)
    (s : ConcreteState Reg) (o : Obs) : Prop :=
  satisfiesSymPC s pw.entryPc ∧
    ExecBlockPathDenotesObs Relevant observe pw.blocks s o

/-- Concrete observation-level denotation of a finite family of path witnesses. -/
def ExecPathWitnessFamilyDenotesObs
    {Reg : Type} {Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop)
    (observe : ConcreteState Reg → Obs)
    (paths : Finset (PathWitness Reg))
    (s : ConcreteState Reg) (o : Obs) : Prop :=
  ∃ pw ∈ paths, ExecPathWitnessDenotesObs Relevant observe pw s o

theorem execPathWitnessFamilyDenotesObs_insert_iff
    {Reg : Type} {Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop)
    (observe : ConcreteState Reg → Obs)
    (pw : PathWitness Reg) (paths : Finset (PathWitness Reg))
    (s : ConcreteState Reg) (o : Obs) :
    ExecPathWitnessFamilyDenotesObs Relevant observe (insert pw paths) s o ↔
      ExecPathWitnessDenotesObs Relevant observe pw s o ∨
        ExecPathWitnessFamilyDenotesObs Relevant observe paths s o := by
  constructor
  · rintro ⟨pw', hMem, hExec⟩
    rw [Finset.mem_insert] at hMem
    rcases hMem with rfl | hMem
    · exact Or.inl hExec
    · exact Or.inr ⟨pw', hMem, hExec⟩
  · intro h
    rcases h with h | h
    · exact ⟨pw, Finset.mem_insert_self _ _, h⟩
    · rcases h with ⟨pw', hMem, hExec⟩
      exact ⟨pw', Finset.mem_insert.mpr (Or.inr hMem), hExec⟩

theorem lowerPathWitnessSummaries_denotesObs_iff_execPathWitness
    {Reg : Type} {Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop)
    (observe : ConcreteState Reg → Obs)
    (pw : PathWitness Reg) (s : ConcreteState Reg) (o : Obs) :
    VexModelDenotesObs Relevant observe (lowerPathWitnessSummaries pw) s o ↔
      ExecPathWitnessDenotesObs Relevant observe pw s o := by
  constructor
  · intro h
    rcases h with ⟨hRel, summary, hMem, hEnabled, hObs⟩
    rcases Finset.mem_image.mp hMem with ⟨baseSummary, hBase, rfl⟩
    have hGuard := (guardSummary_enabled_iff pw.entryPc baseSummary s).mp hEnabled
    have hPath :
        ExecBlockPathDenotesObs Relevant observe pw.blocks s o :=
      (lowerBlockPathSummaries_denotesObs_iff_execBlockPath Relevant observe pw.blocks s o).mp
        ⟨hRel, baseSummary, hBase, hGuard.2, by simpa using hObs⟩
    exact ⟨hGuard.1, hPath⟩
  · rintro ⟨hEntry, hPath⟩
    rcases (lowerBlockPathSummaries_denotesObs_iff_execBlockPath Relevant observe pw.blocks s o).mpr hPath with
      ⟨hRel, baseSummary, hBase, hEnabled, hObs⟩
    refine ⟨hRel, guardSummary pw.entryPc baseSummary, ?_, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨baseSummary, hBase, rfl⟩
    · exact (guardSummary_enabled_iff pw.entryPc baseSummary s).mpr ⟨hEntry, hEnabled⟩
    · simpa using hObs

/-- The guarded summary family of a finite set of path witnesses is an adequate model
of the corresponding valid path-witness family. -/
theorem lowerPathWitnessFamilySummaries_denotesObs_iff_execPathWitnessFamily
    {Reg : Type} {Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg → Prop)
    (observe : ConcreteState Reg → Obs)
    (paths : Finset (PathWitness Reg)) :
    ∀ s o,
      VexModelDenotesObs Relevant observe (lowerPathWitnessFamilySummaries paths) s o ↔
        ExecPathWitnessFamilyDenotesObs Relevant observe paths s o := by
  refine Finset.induction_on paths ?base ?step
  · intro s o
    constructor
    · intro h
      rcases h with ⟨_, summary, hMem, _, _⟩
      simp [lowerPathWitnessFamilySummaries] at hMem
    · intro h
      rcases h with ⟨pw, hMem, _⟩
      simp at hMem
  · intro pw paths hNotMem ih s o
    rw [lowerPathWitnessFamilySummaries, Finset.biUnion_insert]
    change ModelDenotesObs Summary.enabled Summary.apply Relevant observe
        (lowerPathWitnessSummaries pw ∪ paths.biUnion lowerPathWitnessSummaries) s o ↔
      ExecPathWitnessFamilyDenotesObs Relevant observe (insert pw paths) s o
    rw [ModelDenotesObs.union_iff Summary.enabled Summary.apply Relevant observe,
      execPathWitnessFamilyDenotesObs_insert_iff]
    change VexModelDenotesObs Relevant observe (lowerPathWitnessSummaries pw) s o ∨
        VexModelDenotesObs Relevant observe (lowerPathWitnessFamilySummaries paths) s o ↔
      ExecPathWitnessDenotesObs Relevant observe pw s o ∨
        ExecPathWitnessFamilyDenotesObs Relevant observe paths s o
    rw [lowerPathWitnessSummaries_denotesObs_iff_execPathWitness]
    constructor
    · intro h
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr ((ih s o).mp h)
    · intro h
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr ((ih s o).mpr h)

/-- A finite path-witness family for the fetched-trace behavior of a VEX subsystem.
`entryRelevant` is the minimal framework-side precondition tying witness validity
conditions back to the subsystem's relevant-state predicate. -/
structure FetchedSubsystemWitness
    (Reg : Type) (Obs : Type) [DecidableEq Reg] [Fintype Reg] where
  program : Program Reg
  ip_reg : Reg
  Relevant : ConcreteState Reg → Prop
  observe : ConcreteState Reg → Obs
  paths : Finset (PathWitness Reg)
  entryRelevant : ∀ s pw, pw ∈ paths → satisfiesSymPC s pw.entryPc → Relevant s
  complete : ∀ s o,
    ExecProgramTraceDenotesObs Relevant observe program ip_reg s o ↔
      ExecPathWitnessFamilyDenotesObs Relevant observe paths s o

/-- The extracted guarded summary family of a fetched subsystem witness is an adequate
observation-level model of the fetched subsystem trace semantics. -/
def FetchedSubsystemExtractible
    {Reg : Type} {Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (w : FetchedSubsystemWitness Reg Obs) : Prop :=
  ∀ s o,
    VexModelDenotesObs w.Relevant w.observe (lowerPathWitnessFamilySummaries w.paths) s o ↔
      ExecProgramTraceDenotesObs w.Relevant w.observe w.program w.ip_reg s o

/-- Any complete finite fetched-path witness yields an adequate extracted model of the
corresponding fetched subsystem behavior. -/
theorem extractedModel_of_fetchedSubsystemWitness
    {Reg : Type} {Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (w : FetchedSubsystemWitness Reg Obs) :
    FetchedSubsystemExtractible w := by
  intro s o
  exact Iff.trans
    ((lowerPathWitnessFamilySummaries_denotesObs_iff_execPathWitnessFamily
      w.Relevant w.observe w.paths) s o)
    (w.complete s o).symm

/-- Any two complete path-family witnesses for the same fetched subsystem trace semantics
induce observation-equivalent extracted models. -/
theorem completeFetchedWitnesses_modelEq
    {Reg : Type} {Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (program : Program Reg) (ip_reg : Reg)
    (Relevant : ConcreteState Reg → Prop)
    (observe : ConcreteState Reg → Obs)
    (paths₁ paths₂ : Finset (PathWitness Reg))
    (h₁ : ∀ s o,
      ExecProgramTraceDenotesObs Relevant observe program ip_reg s o ↔
        ExecPathWitnessFamilyDenotesObs Relevant observe paths₁ s o)
    (h₂ : ∀ s o,
      ExecProgramTraceDenotesObs Relevant observe program ip_reg s o ↔
        ExecPathWitnessFamilyDenotesObs Relevant observe paths₂ s o) :
    VexModelEq Relevant observe
      (lowerPathWitnessFamilySummaries paths₁)
      (lowerPathWitnessFamilySummaries paths₂) := by
  intro s o
  exact Iff.trans
    (Iff.trans
      ((lowerPathWitnessFamilySummaries_denotesObs_iff_execPathWitnessFamily
        Relevant observe paths₁) s o)
      (h₁ s o).symm)
    (Iff.trans
      (h₂ s o)
      ((lowerPathWitnessFamilySummaries_denotesObs_iff_execPathWitnessFamily
        Relevant observe paths₂) s o).symm)

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
    (paths : Finset (PathWitness Reg)) :
    Finset (Branch (SymSub Reg) (SymPC Reg)) :=
  (lowerPathWitnessFamilySummaries paths).image summaryAsBranch

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
        ExecPathWitnessFamilyDenotesObs w.Relevant (fun state => state) w.paths s s' := by
    simpa [h_observe] using (w.complete s s')
  have hPathObs : ExecPathWitnessFamilyDenotesObs w.Relevant (fun state => state) w.paths s s' :=
    hcomplete.mp hProgObs
  have hModelObs :
      VexModelDenotesObs w.Relevant (fun state => state) (lowerPathWitnessFamilySummaries w.paths) s s' :=
    ((lowerPathWitnessFamilySummaries_denotesObs_iff_execPathWitnessFamily
      w.Relevant (fun state => state) w.paths) s s').mpr hPathObs
  rcases hModelObs with ⟨_, summary, hSummary, hEnabled, hApply⟩
  refine ⟨summaryAsBranch summary, ?_, hEnabled, ?_⟩
  · exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨summary, hSummary, rfl⟩)
  · simpa [FetchedSubsystemBehavior, summaryAsBranch, vexSummaryISA] using hApply

/-- A fetched subsystem witness with identity observation gives soundness of the
    induced branch model for the fetched trace behavior. Entry-side witness validity
    conditions now provide the relevant-state premise. -/
theorem fetchedSubsystem_branchSound
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    [∀ (s : ConcreteState Reg) (φ : SymPC Reg),
      Decidable ((vexSummaryISA Reg).satisfies s φ)]
    (w : FetchedSubsystemWitness Reg (ConcreteState Reg))
    (h_observe : w.observe = fun state => state) :
    BranchModel.Sound (vexSummaryISA Reg)
      (↑(fetchedSubsystemBranchModel w.paths) : Set (Branch (SymSub Reg) (SymPC Reg)))
      (FetchedSubsystemBehavior w.program w.ip_reg w.Relevant) := by
  intro b hb s hsat
  rcases Finset.mem_image.mp (Finset.mem_coe.mp hb) with ⟨summary, hSummary, rfl⟩
  rcases Finset.mem_biUnion.mp hSummary with ⟨pw, hPw, hGuarded⟩
  rcases Finset.mem_image.mp hGuarded with ⟨baseSummary, hBase, hEq⟩
  subst hEq
  have hEnabled' := (guardSummary_enabled_iff pw.entryPc baseSummary s).mp hsat
  have hRel : w.Relevant s := w.entryRelevant s pw hPw hEnabled'.1
  have hModelObs :
      VexModelDenotesObs w.Relevant (fun state => state)
        (lowerPathWitnessFamilySummaries w.paths) s (Summary.apply baseSummary s) :=
    ⟨hRel, guardSummary pw.entryPc baseSummary, hSummary, hsat, by simp⟩
  have hPathObs :
      ExecPathWitnessFamilyDenotesObs w.Relevant (fun state => state)
        w.paths s (Summary.apply baseSummary s) :=
    ((lowerPathWitnessFamilySummaries_denotesObs_iff_execPathWitnessFamily
      w.Relevant (fun state => state) w.paths) s (Summary.apply baseSummary s)).mp hModelObs
  have hcomplete :
      ExecProgramTraceDenotesObs w.Relevant (fun state => state)
          w.program w.ip_reg s (Summary.apply baseSummary s) ↔
        ExecPathWitnessFamilyDenotesObs w.Relevant (fun state => state)
          w.paths s (Summary.apply baseSummary s) := by
    simpa [h_observe] using (w.complete s (Summary.apply baseSummary s))
  have hProgObs :
      ExecProgramTraceDenotesObs w.Relevant (fun state => state)
        w.program w.ip_reg s (Summary.apply baseSummary s) :=
    hcomplete.mpr hPathObs
  rcases hProgObs with ⟨hRel', _, hTrace, rfl⟩
  exact ⟨hRel', hTrace⟩

/-- A fetched subsystem witness with identity observation yields a semantic-closure
    STS1-style quotient for its flattened witness-path branch model. -/
theorem fetchedSubsystemRefinementBisimulation
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    [∀ (s : ConcreteState Reg) (φ : SymPC Reg),
      Decidable ((vexSummaryISA Reg).satisfies s φ)]
    (w : FetchedSubsystemWitness Reg (ConcreteState Reg))
    (h_observe : w.observe = fun state => state)
    (closure : Finset (SymPC Reg))
    (h_contains : ∀ b ∈ fetchedSubsystemBranchModel w.paths, b.pc ∈ closure)
    (h_semClosed : SemClosed (vexSummaryISA Reg) (fetchedSubsystemBranchModel w.paths) closure) :
    CrossBisimulation
      (Quotient.mk (pcSetoidWith (vexSummaryISA Reg) closure))
    (FetchedSubsystemBehavior w.program w.ip_reg w.Relevant)
      (abstractBehaviorWith (vexSummaryISA Reg) (fetchedSubsystemBranchModel w.paths) closure) := by
  exact quotient_bisimulationSem (vexSummaryISA Reg)
    (fetchedSubsystemBranchModel w.paths) closure
    h_contains h_semClosed
    (FetchedSubsystemBehavior w.program w.ip_reg w.Relevant)
    (fetchedSubsystem_branchSound w h_observe)
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
