import Instances.Examples.Tier0Increment
import Instances.ISAs.VexSubsystem

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA

namespace Instances.Examples.FetchedCFGRefinement

abbrev Reg := Instances.Examples.ToyReg

def block0 : Block Reg :=
  { stmts := [Stmt.put .r0 (.add64 (.get .r0) (.const 1))]
    ip_reg := .r1
    next := 1 }

def program : Program Reg where
  blocks
    | 0 => some block0
    | _ => none

def Relevant (s : ConcreteState Reg) : Prop :=
  s.read .r1 = 0

def entryPc0 : SymPC Reg :=
  .eq (.reg .r1) (.const 0)

abbrev emptyWitness : PathWitness Reg :=
  { entryPc := entryPc0, blocks := [] }

abbrev oneWitness : PathWitness Reg :=
  { entryPc := entryPc0, blocks := [block0] }

def witnessPaths : Finset (PathWitness Reg) :=
  { emptyWitness, oneWitness }

noncomputable local instance :
    ∀ (s : ConcreteState Reg) (φ : SymPC Reg),
      Decidable ((vexSummaryISA Reg).satisfies s φ) := by
  intro s φ
  simpa [satisfiesSymPC] using
    (inferInstance : Decidable (evalSymPC s φ = true))

def expectedEmpty : Summary Reg :=
  guardSummary entryPc0 Summary.id

def expectedOne : Summary Reg :=
  guardSummary entryPc0 (Summary.compose (lowerBlock block0) Summary.id)

private theorem entryPc0_relevant {s : ConcreteState Reg} :
    satisfiesSymPC s entryPc0 → Relevant s := by
  intro h
  simpa [entryPc0, Relevant, satisfiesSymPC, evalSymPC] using h

private theorem fetchBlock_from_relevant
    {s : ConcreteState Reg}
    (hRel : Relevant s) :
    fetchBlock program .r1 s = some block0 := by
  have hip : currentIp .r1 s = 0 := by
    simpa [currentIp, Relevant] using hRel
  simp [fetchBlock, program, hip]

private theorem no_programStep_after_block0
    (s : ConcreteState Reg) :
    ¬ ∃ s', ProgramStep program .r1 (execBlock block0 s) s' := by
  intro h
  rcases h with ⟨s', hStep⟩
  rcases hStep with ⟨block, hFetch, _⟩
  simp [fetchBlock, currentIp, program, block0, execBlock] at hFetch

private theorem self_mem_execBlockPath_nil
    (s : ConcreteState Reg) :
    s ∈ execBlockPath ([] : List (Block Reg)) s := by
  simp [execBlockPath]

private theorem execBlock0_mem_execBlockPath_singleton
    (s : ConcreteState Reg) :
    execBlock block0 s ∈ execBlockPath [block0] s := by
  simp [execBlockPath, execBlockSuccs, block0, execBlock]

private theorem trace_from_relevant_cases
    {s s' : ConcreteState Reg}
    (hRel : Relevant s)
    (hTrace : Relation.ReflTransGen (ProgramStep program .r1) s s') :
    s' = s ∨ s' = execBlock block0 s := by
  induction hTrace with
  | refl =>
      exact Or.inl rfl
  | @tail b c hPrev hStep ih =>
      rcases ih with rfl | hOne
      · exact Or.inr <| by
          rcases hStep with ⟨block, hFetch, hSyntax⟩
          have hb : block = block0 := by
            rw [fetchBlock_from_relevant hRel] at hFetch
            exact Option.some.inj hFetch.symm
          subst hb
          simpa [SyntaxDenotes, block0, execBlockSuccs, execBlock] using hSyntax
      · exfalso
        subst hOne
        exact no_programStep_after_block0 s ⟨c, hStep⟩

private theorem witnessCompleteState :
    ∀ s0 s1,
      ExecProgramTraceDenotesObs Relevant (fun t => t) program .r1 s0 s1 ↔
        ExecPathWitnessFamilyDenotesObs Relevant (fun t => t) witnessPaths s0 s1 := by
  intro s0 s1
  constructor
  · intro h
    rcases h with ⟨hRel, t, hTrace, hEq⟩
    subst hEq
    rcases trace_from_relevant_cases hRel hTrace with rfl | hOne
    · have hExec : ExecPathWitnessDenotesObs Relevant (fun t => t) emptyWitness t t := by
        have hPath : t ∈ execBlockPath ([] : List (Block Reg)) t := by
          exact self_mem_execBlockPath_nil t
        refine ⟨?_, hRel, t, ?_, rfl⟩
        · simpa [entryPc0, Relevant, satisfiesSymPC, evalSymPC] using hRel
        · exact hPath
      simpa using
        (show ExecPathWitnessFamilyDenotesObs Relevant (fun t => t) witnessPaths t t from
          ⟨emptyWitness, by simp [witnessPaths], hExec⟩)
    · have hExec :
          ExecPathWitnessDenotesObs Relevant (fun t => t) oneWitness s0 (execBlock block0 s0) := by
        refine ⟨?_, hRel, execBlock block0 s0, ?_, rfl⟩
        · simpa [entryPc0, Relevant, satisfiesSymPC, evalSymPC] using hRel
        · simpa [execBlockPath] using execBlock0_mem_execBlockPath_singleton s0
      simpa [hOne] using
        (show ExecPathWitnessFamilyDenotesObs Relevant (fun t => t) witnessPaths s0 (execBlock block0 s0) from
          ⟨oneWitness, by simp [witnessPaths], hExec⟩)
  · intro h
    rcases h with ⟨pw, hMem, hExec⟩
    simp [witnessPaths] at hMem
    rcases hMem with rfl | rfl
    · rcases hExec with ⟨hEntry, hRel, t, hPath, hEq⟩
      have ht : t = s0 := by simpa [execBlockPath] using hPath
      subst ht
      exact ⟨hRel, t, Relation.ReflTransGen.refl, hEq⟩
    · rcases hExec with ⟨hEntry, hRel, t, hPath, hEq⟩
      have hStep : ProgramStep program .r1 s0 t := by
        refine ⟨block0, fetchBlock_from_relevant hRel, ?_⟩
        simpa [SyntaxDenotes, execBlockPath] using hPath
      exact ⟨hRel, t, Relation.ReflTransGen.tail Relation.ReflTransGen.refl hStep, hEq⟩

def witnessState : FetchedSubsystemWitness Reg (ConcreteState Reg) where
  program := program
  ip_reg := .r1
  Relevant := Relevant
  observe := fun s => s
  paths := witnessPaths
  entryRelevant := by
    intro s pw hMem hEntry
    simp [witnessPaths] at hMem
    rcases hMem with rfl | rfl
    · exact entryPc0_relevant hEntry
    · exact entryPc0_relevant hEntry
  complete := by
    intro s s'
    exact witnessCompleteState s s'

def closure : Finset (SymPC Reg) := { expectedEmpty.pc, expectedOne.pc }

private theorem expectedEmpty_pc :
    expectedEmpty.pc = SymPC.and entryPc0 SymPC.true := by
  native_decide

private theorem expectedOne_pc :
    expectedOne.pc = SymPC.and entryPc0 (SymPC.and SymPC.true SymPC.true) := by
  native_decide

private theorem branchModel_eq :
    fetchedSubsystemBranchModel witnessState.paths =
      {summaryAsBranch expectedEmpty, summaryAsBranch expectedOne} := by
  native_decide

private theorem h_contains :
    ∀ b ∈ fetchedSubsystemBranchModel witnessState.paths, b.pc ∈ closure := by
  intro b hb
  rw [branchModel_eq] at hb
  have hb' : b = summaryAsBranch expectedEmpty ∨ b = summaryAsBranch expectedOne := by
    simpa using hb
  rcases hb' with rfl | rfl
  · simp [closure, expectedEmpty_pc]
  · simp [closure, expectedOne_pc]

private theorem one_lift_expectedEmpty_pc :
    substSymPC expectedOne.sub expectedEmpty.pc =
      SymPC.and (SymPC.eq (.const 1) (.const 0)) SymPC.true := by
  native_decide

private theorem one_lift_expectedOne_pc :
    substSymPC expectedOne.sub expectedOne.pc =
      SymPC.and (SymPC.eq (.const 1) (.const 0)) (SymPC.and SymPC.true SymPC.true) := by
  native_decide

private theorem empty_lift_expectedEmpty_pc :
    substSymPC expectedEmpty.sub expectedEmpty.pc = expectedEmpty.pc := by
  native_decide

private theorem empty_lift_expectedOne_pc :
    substSymPC expectedEmpty.sub expectedOne.pc = expectedOne.pc := by
  native_decide

private theorem lifted_expectedEmpty_after_one_disabled (s : ConcreteState Reg) :
    ¬ satisfiesSymPC s (substSymPC expectedOne.sub expectedEmpty.pc) := by
  rw [one_lift_expectedEmpty_pc]
  simp [satisfiesSymPC, evalSymPC, evalSymExpr]

private theorem lifted_expectedOne_after_one_disabled (s : ConcreteState Reg) :
    ¬ satisfiesSymPC s (substSymPC expectedOne.sub expectedOne.pc) := by
  rw [one_lift_expectedOne_pc]
  simp [satisfiesSymPC, evalSymPC, evalSymExpr]

private theorem h_semClosed :
    SemClosed (vexSummaryISA Reg) (fetchedSubsystemBranchModel witnessState.paths) closure := by
  intro b hb φ hφ s₁ s₂ hEq
  rw [branchModel_eq] at hb
  have hφ' : φ = expectedEmpty.pc ∨ φ = expectedOne.pc := by
    simpa [closure] using hφ
  simp at hb
  rcases hb with rfl | rfl <;> rcases hφ' with rfl | rfl
  · simpa [empty_lift_expectedEmpty_pc] using
      hEq expectedEmpty.pc (by simp [closure])
  · simpa [empty_lift_expectedOne_pc] using
      hEq expectedOne.pc (by simp [closure])
  · constructor
    · intro h
      exact False.elim ((lifted_expectedEmpty_after_one_disabled s₁) h)
    · intro h
      exact False.elim ((lifted_expectedEmpty_after_one_disabled s₂) h)
  · constructor
    · intro h
      exact False.elim ((lifted_expectedOne_after_one_disabled s₁) h)
    · intro h
      exact False.elim ((lifted_expectedOne_after_one_disabled s₂) h)

example :
    CrossBisimulation
      (Quotient.mk (pcSetoidWith (vexSummaryISA Reg) closure))
      (FetchedSubsystemBehavior program .r1 Relevant)
      (abstractBehaviorWith (vexSummaryISA Reg) (fetchedSubsystemBranchModel witnessState.paths) closure) := by
  exact fetchedSubsystemRefinementBisimulation witnessState rfl closure h_contains h_semClosed

noncomputable example :
    Fintype.card (Quotient (pcSetoidWith (vexSummaryISA Reg) closure)) ≤ 2 ^ closure.card := by
  exact fetchedSubsystemRefinement_card_bound (Reg := Reg) closure

end Instances.Examples.FetchedCFGRefinement
