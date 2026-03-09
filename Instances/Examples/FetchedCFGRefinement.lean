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

/-- A fetched block that writes the program IP register to a constant.
    Executing it twice has the same effect as executing it once. -/
def block : Block Reg :=
  { stmts := [Stmt.put .r1 (.const 1)]
    ip_reg := .r1
    next := 1 }

private theorem execBlock_eq_write
    (s : ConcreteState Reg) :
    execBlock block s = s.write .r1 1 := by
  ext reg <;> simp [block, execBlock, execStmt, execLinearStmt, linearStmtBridge, ConcreteState.write]

def program : Program Reg where
  blocks _ := some block

def witnessPaths : Finset (List (Block Reg)) :=
  {[], [block]}

private theorem execBlock_idempotent
    (s : ConcreteState Reg) :
    execBlock block (execBlock block s) = execBlock block s := by
  rw [execBlock_eq_write, execBlock_eq_write]
  ext reg <;> simp [ConcreteState.write]

private theorem self_mem_execBlockPath_nil
    (s : ConcreteState Reg) :
    s ∈ execBlockPath ([] : List (Block Reg)) s := by
  simp [execBlockPath]

private theorem execBlock_mem_execBlockPath_singleton
    (s : ConcreteState Reg) :
    execBlock block s ∈ execBlockPath [block] s := by
  simp [execBlockPath, execBlockSuccs, block, execBlock]

def expectedSummary : Summary Reg := lowerBlock block

def expectedPathSummary : Summary Reg := Summary.compose expectedSummary Summary.id

private theorem lowerPathFamilySummaries_eq_expected :
    lowerPathFamilySummaries witnessPaths = {Summary.id, expectedPathSummary} := by
  native_decide

private theorem trace_cases
    (s s' : ConcreteState Reg)
    (hTrace : Relation.ReflTransGen (ProgramStep program .r1) s s') :
    s' = s ∨ s' = execBlock block s := by
  induction hTrace with
  | refl =>
      exact Or.inl rfl
  | @tail b c hPrev hStep ih =>
      rcases ih with rfl | hExec
      · exact Or.inr <| by
          rcases hStep with ⟨block', hFetch, hSyntax⟩
          have hb : block' = block := by
            simp [fetchBlock, currentIp, program] at hFetch
            exact hFetch.symm
          subst hb
          simpa [SyntaxDenotes, block, execBlockSuccs, execBlock] using hSyntax
      · exact Or.inr <| by
          subst hExec
          rcases hStep with ⟨block', hFetch, hSyntax⟩
          have hb : block' = block := by
            simp [fetchBlock, currentIp, program] at hFetch
            exact hFetch.symm
          subst hb
          have hc : c = execBlock block (execBlock block s) := by
            simpa [SyntaxDenotes, block, execBlockSuccs, execBlock] using hSyntax
          simpa [execBlock_idempotent] using hc

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
      have hs' : s' = execBlock block s := by
        simpa [execBlockPath, SyntaxDenotes, block, execBlockSuccs, execBlock] using hPath
      subst hs'
      have hStep : ProgramStep program .r1 s (execBlock block s) := by
        refine ⟨block, by simp [fetchBlock, currentIp, program], ?_⟩
        simp [SyntaxDenotes, block, execBlockSuccs, execBlock]
      exact ⟨trivial, _, Relation.ReflTransGen.tail Relation.ReflTransGen.refl hStep, hObs⟩
  · intro h
    rcases h with ⟨_, s', hTrace, hObs⟩
    have hs' : s' = s ∨ s' = execBlock block s :=
      trace_cases s s' hTrace
    rcases hs' with hs' | hs'
    · refine ⟨[], by simp [witnessPaths], ⟨trivial, s', ?_, hObs⟩⟩
      simpa [hs'] using self_mem_execBlockPath_nil s
    · refine ⟨[block], by simp [witnessPaths], ⟨trivial, s', ?_, hObs⟩⟩
      simpa [hs'] using execBlock_mem_execBlockPath_singleton s

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
  rcases Finset.mem_image.mp hb with ⟨summary, hMem, rfl⟩
  have hsMem : summary ∈ ({Summary.id, expectedPathSummary} : Finset (Summary Reg)) := by
    simpa [lowerPathFamilySummaries_eq_expected] using hMem
  have hs : summary = Summary.id ∨ summary = expectedPathSummary := by
    simpa using hsMem
  rcases hs with rfl | rfl <;> simp [closure, summaryAsBranch, expectedPathSummary]

private theorem h_closed :
    ∀ b ∈ fetchedSubsystemBranchModel witness.paths, ∀ φ ∈ closure,
      (vexSummaryISA Reg).pc_lift b.sub φ ∈ closure := by
  intro b hb φ hφ
  rcases Finset.mem_image.mp hb with ⟨summary, hMem, rfl⟩
  have hsMem : summary ∈ ({Summary.id, expectedPathSummary} : Finset (Summary Reg)) := by
    simpa [lowerPathFamilySummaries_eq_expected] using hMem
  have hs : summary = Summary.id ∨ summary = expectedPathSummary := by
    simpa using hsMem
  have : φ = SymPC.true := by simpa [closure] using hφ
  subst this
  rcases hs with rfl | rfl <;> simp [closure, vexSummaryISA, expectedPathSummary]

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
