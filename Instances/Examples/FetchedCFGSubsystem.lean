import Instances.Examples.Tier0Increment
import Instances.ISAs.VexSubsystem

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA

namespace Instances.Examples.FetchedCFGSubsystem

abbrev Reg := Instances.Examples.ToyReg

/-- First block: increment `r0`, then move to ip = 1. -/
def block0 : Block Reg :=
  { stmts := [Stmt.put .r0 (.add64 (.get .r0) (.const 1))]
    ip_reg := .r1
    next := 1 }

/-- Second block: increment `r0` again, then leave the subsystem. -/
def block1 : Block Reg :=
  { stmts := [Stmt.put .r0 (.add64 (.get .r0) (.const 1))]
    ip_reg := .r1
    next := 2 }

abbrev path01 : List (Block Reg) := [block0, block1]

def program : Program Reg where
  blocks
    | 0 => some block0
    | 1 => some block1
    | _ => none

def Relevant (s : ConcreteState Reg) : Prop :=
  s.read .r1 = 0

def observe (s : ConcreteState Reg) : UInt64 × UInt64 :=
  (s.read .r0, s.read .r1)

def witnessPaths : Finset (List (Block Reg)) :=
  {[], [block0], path01}

private theorem fetchBlock_from_relevant
    {s : ConcreteState Reg}
    (hRel : Relevant s) :
    fetchBlock program .r1 s = some block0 := by
  have hip : currentIp .r1 s = 0 := by
    simpa [currentIp, Relevant] using hRel
  simp [fetchBlock, program, hip]

private theorem fetchBlock_after_block0
    (s : ConcreteState Reg) :
    fetchBlock program .r1 (execBlock block0 s) = some block1 := by
  simp [fetchBlock, currentIp, program, block0, execBlock]

private theorem no_programStep_after_block1
    (s : ConcreteState Reg) :
    ¬ ∃ s', ProgramStep program .r1 (execBlock block1 (execBlock block0 s)) s' := by
  intro h
  rcases h with ⟨s', hStep⟩
  rcases hStep with ⟨block, hFetch, _⟩
  simp [fetchBlock, currentIp, program, block1, execBlock] at hFetch

private theorem self_mem_execBlockPath_nil
    (s : ConcreteState Reg) :
    s ∈ execBlockPath ([] : List (Block Reg)) s := by
  simp [execBlockPath]

private theorem execBlock0_mem_execBlockPath_singleton
    (s : ConcreteState Reg) :
    execBlock block0 s ∈ execBlockPath [block0] s := by
  simp [execBlockPath, execBlockSuccs, block0, execBlock]

private theorem execBlock01_mem_execBlockPath_pair
    (s : ConcreteState Reg) :
    execBlock block1 (execBlock block0 s) ∈ execBlockPath path01 s := by
  simp [execBlockPath, execBlockSuccs, block0, block1, execBlock]

private theorem trace_from_relevant_cases
    {s s' : ConcreteState Reg}
    (hRel : Relevant s)
    (hTrace : Relation.ReflTransGen (ProgramStep program .r1) s s') :
    s' = s ∨ s' = execBlock block0 s ∨ s' = execBlock block1 (execBlock block0 s) := by
  induction hTrace with
  | refl =>
      exact Or.inl rfl
  | @tail b c hPrev hStep ih =>
      rcases ih with rfl | hOne | hTwo
      · exact Or.inr <| Or.inl <| by
          rcases hStep with ⟨block, hFetch, hSyntax⟩
          have hb : block = block0 := by
            rw [fetchBlock_from_relevant hRel] at hFetch
            exact Option.some.inj hFetch.symm
          subst hb
          simpa [SyntaxDenotes, block0, execBlockSuccs, execBlock] using hSyntax
      · subst hOne
        exact Or.inr <| Or.inr <| by
          rcases hStep with ⟨block, hFetch, hSyntax⟩
          have hb : block = block1 := by
            rw [fetchBlock_after_block0 s] at hFetch
            exact Option.some.inj hFetch.symm
          subst hb
          simpa [SyntaxDenotes, block1, execBlockSuccs, execBlock]
            using hSyntax
      · exfalso
        subst hTwo
        exact no_programStep_after_block1 s ⟨c, hStep⟩

private theorem witnessComplete :
    WitnessComplete
      { Relevant := Relevant, observe := observe,
        DenotesObs := ExecProgramTraceDenotesObs Relevant observe program .r1 }
      witnessPaths := by
  intro s o
  constructor
  · intro h
    rcases h with ⟨blocks, hMem, hExec⟩
    simp [witnessPaths] at hMem
    rcases hMem with rfl | rfl | rfl
    · rcases hExec with ⟨hRel, s', hPath, hObs⟩
      have hs' : s' = s := by simpa [execBlockPath] using hPath
      subst hs'
      exact ⟨hRel, _, Relation.ReflTransGen.refl, hObs⟩
    · rcases hExec with ⟨hRel, s', hPath, hObs⟩
      have hStep : ProgramStep program .r1 s s' := by
        refine ⟨block0, fetchBlock_from_relevant hRel, ?_⟩
        simpa [SyntaxDenotes, execBlockPath] using hPath
      exact ⟨hRel, s', Relation.ReflTransGen.tail Relation.ReflTransGen.refl hStep, hObs⟩
    · rcases hExec with ⟨hRel, s', hPath, hObs⟩
      have hMid : ProgramStep program .r1 s (execBlock block0 s) := by
        refine ⟨block0, fetchBlock_from_relevant hRel, ?_⟩
        simp [SyntaxDenotes, block0, execBlockSuccs, execBlock]
      have hTail : ProgramStep program .r1 (execBlock block0 s) s' := by
        refine ⟨block1, fetchBlock_after_block0 s, ?_⟩
        simpa [path01, SyntaxDenotes, execBlockPath, execBlockSuccs, block0, block1, execBlock] using hPath
      exact ⟨hRel, s', Relation.ReflTransGen.tail (Relation.ReflTransGen.tail Relation.ReflTransGen.refl hMid) hTail, hObs⟩
  · intro h
    rcases h with ⟨hRel, s', hTrace, hObs⟩
    rcases trace_from_relevant_cases hRel hTrace with hs' | hOne | hTwo
    · refine ⟨[], by simp [witnessPaths], ⟨hRel, s', ?_, hObs⟩⟩
      simpa [hs'] using self_mem_execBlockPath_nil s
    · refine ⟨[block0], by simp [witnessPaths], ⟨hRel, s', ?_, hObs⟩⟩
      simpa [hOne] using execBlock0_mem_execBlockPath_singleton s
    · refine ⟨path01, by simp [witnessPaths], ⟨hRel, s', ?_, hObs⟩⟩
      simpa [hTwo] using execBlock01_mem_execBlockPath_pair s

def witness : FetchedSubsystemWitness Reg (UInt64 × UInt64) where
  program := program
  ip_reg := .r1
  Relevant := Relevant
  observe := observe
  paths := witnessPaths
  complete := by
    intro s o
    exact (witnessComplete s o).symm

example : FetchedSubsystemExtractible witness :=
  extractedModel_of_fetchedSubsystemWitness witness

example :
    ∀ s o,
      VexModelDenotesObs Relevant observe (lowerPathFamilySummaries witnessPaths) s o ↔
        ExecProgramTraceDenotesObs Relevant observe program .r1 s o := by
  exact extractedModel_of_fetchedSubsystemWitness witness

end Instances.Examples.FetchedCFGSubsystem
