import Instances.Examples.Tier0Increment
import Instances.ISAs.VexSubsystem

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA

namespace Instances.Examples.FetchedCFGRefinement

abbrev Reg := Instances.Examples.ToyReg

noncomputable local instance :
    ∀ (s : ConcreteState Reg) (φ : SymPC Reg),
      Decidable ((vexSummaryISA Reg).satisfies s φ) := by
  intro s φ
  simpa [satisfiesSymPC] using
    (inferInstance : Decidable (evalSymPC s φ = true))

def block : Block Reg :=
  { stmts := [Stmt.put .r0 (.add64 (.get .r0) (.const 1))]
    ip_reg := .r1
    next := 1 }

def program : Program Reg where
  blocks
    | 1 => none
    | _ => some block

def witnessPaths : Finset (List (Block Reg)) :=
  {[], [block]}

private theorem fetchBlock_not_halt
    (s : ConcreteState Reg) (h1 : s.read .r1 ≠ 1) :
    fetchBlock program .r1 s = some block := by
  change (match s.regs .r1 with | 1 => none | _ => some block) = some block
  by_cases h : s.regs .r1 = 1
  · exfalso
    exact h1 (by simpa using h)
  · simp [h]

private theorem no_programStep_halt
    (s : ConcreteState Reg) (h1 : s.read .r1 = 1) :
    ¬ ∃ s', ProgramStep program .r1 s s' := by
  intro h
  rcases h with ⟨s', hStep⟩
  rcases hStep with ⟨block', hFetch, _⟩
  change (match s.regs .r1 with | 1 => none | _ => some block) = some block' at hFetch
  rw [show s.regs .r1 = 1 by simpa using h1] at hFetch
  simp at hFetch

private theorem self_mem_execBlockPath_nil
    (s : ConcreteState Reg) :
    s ∈ execBlockPath ([] : List (Block Reg)) s := by
  simp [execBlockPath]

private theorem execBlock_mem_execBlockPath_singleton
    (s : ConcreteState Reg) :
    execBlock block s ∈ execBlockPath [block] s := by
  simp [execBlockPath, execBlockSuccs, block, execBlock]

private theorem witnessComplete :
    WitnessComplete
      { Relevant := fun _ => True
        observe := fun s => s
        DenotesObs := ExecProgramTraceDenotesObs (fun _ => True) (fun s => s) program .r1 }
      witnessPaths := by
  intro s o
  constructor
  · intro h
    rcases h with ⟨blocks, hMem, hExec⟩
    simp [witnessPaths] at hMem
    rcases hMem with rfl | rfl
    · rcases hExec with ⟨_, s', hPath, hObs⟩
      have hs' : s' = s := by simpa [execBlockPath] using hPath
      subst hs'
      exact ⟨trivial, _, Relation.ReflTransGen.refl, hObs⟩
    · rcases hExec with ⟨_, s', hPath, hObs⟩
      have hStep : ProgramStep program .r1 s s' := by
        refine ⟨block, fetchBlock_not_halt s ?_, ?_⟩
        · intro h1
          have hs' : s' = execBlock block s := by
            simpa [execBlockPath, SyntaxDenotes, block, execBlockSuccs, execBlock] using hPath
          have hsEq := congrArg (fun st => st.read .r1) hs'
          simp [block, execBlock, h1] at hsEq
        · simpa [SyntaxDenotes, execBlockPath, block, execBlockSuccs, execBlock] using hPath
      exact ⟨trivial, s', Relation.ReflTransGen.tail Relation.ReflTransGen.refl hStep, hObs⟩
  · intro h
    rcases h with ⟨_, s', hTrace, hObs⟩
    by_cases h1 : s.read .r1 = 1
    · cases hTrace with
      | refl =>
          refine ⟨[], by simp [witnessPaths], ⟨trivial, s', ?_, hObs⟩⟩
          simpa using self_mem_execBlockPath_nil s
      | tail hPrev hStep =>
          cases hPrev with
          | refl =>
              exfalso
              exact no_programStep_halt s h1 ⟨_, hStep⟩
          | tail hPrev hStep =>
              exfalso
              exact no_programStep_halt s h1 ⟨_, hStep⟩
    · cases hTrace with
      | refl =>
          refine ⟨[], by simp [witnessPaths], ⟨trivial, s', ?_, hObs⟩⟩
          simpa using self_mem_execBlockPath_nil s
      | tail hPrev hStep =>
          cases hPrev with
          | refl =>
              refine ⟨[block], by simp [witnessPaths], ⟨trivial, s', ?_, hObs⟩⟩
              rcases hStep with ⟨block', hFetch, hSyntax⟩
              have hb : block' = block := by
                rw [fetchBlock_not_halt s h1] at hFetch
                exact Option.some.inj hFetch.symm
              subst hb
              simpa [SyntaxDenotes, execBlockPath, block, execBlockSuccs, execBlock] using hSyntax
          | tail hPrev hStep =>
              exfalso
              have hs : s' = execBlock block s := by
                cases hPrev with
                | refl =>
                    rcases hStep with ⟨block', hFetch, hSyntax⟩
                    have hb : block' = block := by
                      rw [fetchBlock_not_halt s h1] at hFetch
                      exact Option.some.inj hFetch.symm
                    subst hb
                    simpa [SyntaxDenotes, block, execBlockSuccs, execBlock] using hSyntax
              subst hs
              exact no_programStep_halt (execBlock block s) (by simp [block, execBlock]) ⟨_, hStep⟩

def witness : FetchedSubsystemWitness Reg (ConcreteState Reg) where
  program := program
  ip_reg := .r1
  Relevant := fun _ => True
  observe := fun s => s
  paths := witnessPaths
  complete := by
    intro s o
    exact (witnessComplete s o).symm

def closure : Finset (SymPC Reg) := {SymPC.true}

private theorem h_contains : ∀ b ∈ fetchedSubsystemBranchModel witness.paths, b.pc ∈ closure := by
  intro b hb
  rcases Finset.mem_image.mp (Finset.mem_coe.mp hb) with ⟨summary, _, rfl⟩
  simp [closure, summaryAsBranch]

private theorem h_closed :
    ∀ b ∈ fetchedSubsystemBranchModel witness.paths, ∀ φ ∈ closure,
      (vexSummaryISA Reg).pc_lift b.sub φ ∈ closure := by
  intro b hb φ hφ
  rcases Finset.mem_image.mp (Finset.mem_coe.mp hb) with ⟨summary, _, rfl⟩
  have : φ = SymPC.true := by simpa [closure] using hφ
  subst this
  simp [closure, vexSummaryISA]

private theorem h_semClosed :
    SemClosed (vexSummaryISA Reg) (fetchedSubsystemBranchModel witness.paths) closure :=
  semClosed_of_syntacticallyClosed (vexSummaryISA Reg)
    (fetchedSubsystemBranchModel witness.paths) closure h_closed

private theorem h_relevant :
    ∀ s, ∀ summary ∈ lowerPathFamilySummaries witness.paths,
      Summary.enabled summary s → witness.Relevant s := by
  intro _ _ _ _
  trivial

example :
    CrossBisimulation
      (Quotient.mk (pcSetoidWith (vexSummaryISA Reg) closure))
      (FetchedSubsystemBehavior witness.program witness.ip_reg witness.Relevant)
      (abstractBehaviorWith (vexSummaryISA Reg) (fetchedSubsystemBranchModel witness.paths) closure) := by
  exact fetchedSubsystemRefinementBisimulation witness rfl closure h_contains h_semClosed h_relevant

noncomputable example :
    Fintype.card (Quotient (pcSetoidWith (vexSummaryISA Reg) closure)) ≤ 2 ^ closure.card := by
  exact fetchedSubsystemRefinement_card_bound (Reg := Reg) closure

end Instances.Examples.FetchedCFGRefinement
