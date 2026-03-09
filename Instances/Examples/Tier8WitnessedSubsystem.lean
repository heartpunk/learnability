import Instances.Examples.Tier0Increment
import Instances.ISAs.VexWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA

namespace Instances.Examples.Tier8WitnessedSubsystem

abbrev Reg := Instances.Examples.ToyReg

/-- One-block subsystem: increment `r0`, then leave the subsystem by setting `ip = 1`. -/
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

def observe (s : ConcreteState Reg) : UInt64 × UInt64 :=
  (s.read .r0, s.read .r1)

def witnessPaths : Finset (List (Block Reg)) :=
  {[], [block0]}

def region : Region Reg (UInt64 × UInt64) :=
  { Relevant := Relevant
    observe := observe
    DenotesObs := ExecProgramTraceDenotesObs Relevant observe program .r1 }

private theorem fetchBlock_from_relevant
    {s : ConcreteState Reg}
    (hRel : Relevant s) :
    fetchBlock program .r1 s = some block0 := by
  have hip : currentIp .r1 s = 0 := by
    simpa [currentIp, Relevant] using hRel
  simp [fetchBlock, program, hip]

private theorem self_mem_execBlockPath_nil
    (s : ConcreteState Reg) :
    s ∈ execBlockPath ([] : List (Block Reg)) s := by
  simp [execBlockPath]

private theorem execBlock_mem_execBlockPath_singleton
    (s : ConcreteState Reg) :
    execBlock block0 s ∈ execBlockPath [block0] s := by
  simp [execBlockPath, execBlockSuccs, execBlock, block0]

private theorem programStep_from_relevant_eq_execBlock
    {s s' : ConcreteState Reg}
    (hRel : Relevant s)
    (hStep : ProgramStep program .r1 s s') :
    s' = execBlock block0 s := by
  rcases hStep with ⟨block, hFetch, hSyntax⟩
  have hFetch' : fetchBlock program .r1 s = some block0 :=
    fetchBlock_from_relevant hRel
  have hb : block = block0 := by
    rw [hFetch'] at hFetch
    exact Option.some.inj hFetch.symm
  subst hb
  simpa [SyntaxDenotes, block0, execBlockSuccs, execBlock] using hSyntax

private theorem no_programStep_after_execBlock
    (s : ConcreteState Reg) :
    ¬ ∃ s', ProgramStep program .r1 (execBlock block0 s) s' := by
  intro h
  rcases h with ⟨s', hStep⟩
  rcases hStep with ⟨block, hFetch, _hSyntax⟩
  simp [program, fetchBlock, currentIp, block0, execBlock] at hFetch

private theorem trace_from_relevant_cases
    {s s' : ConcreteState Reg}
    (hRel : Relevant s)
    (hTrace : Relation.ReflTransGen (ProgramStep program .r1) s s') :
    s' = s ∨ s' = execBlock block0 s := by
  induction hTrace with
  | refl =>
      exact Or.inl rfl
  | @tail b c hPrev hStep ih =>
      rcases ih with rfl | hb
      · exact Or.inr (programStep_from_relevant_eq_execBlock hRel hStep)
      · exfalso
        subst hb
        exact no_programStep_after_execBlock s ⟨c, hStep⟩

private theorem witnessComplete : WitnessComplete region witnessPaths := by
  intro s o
  constructor
  · intro h
    rcases h with ⟨blocks, hMem, hExec⟩
    simp [witnessPaths] at hMem
    rcases hMem with rfl | rfl
    · rcases hExec with ⟨hRel, s', hPath, hObs⟩
      have hs' : s' = s := by
        simpa [execBlockPath] using hPath
      subst hs'
      exact ⟨hRel, _, Relation.ReflTransGen.refl, hObs⟩
    · rcases hExec with ⟨hRel, s', hPath, hObs⟩
      have hStep : ProgramStep program .r1 s s' := by
        refine ⟨block0, ?_, ?_⟩
        · exact fetchBlock_from_relevant hRel
        · simpa [SyntaxDenotes, execBlockPath] using hPath
      exact ⟨hRel, s', Relation.ReflTransGen.tail Relation.ReflTransGen.refl hStep, hObs⟩
  · intro h
    rcases h with ⟨hRel, s', hTrace, hObs⟩
    rcases trace_from_relevant_cases hRel hTrace with hs' | hs'
    · refine ⟨[], by simp [witnessPaths], ⟨hRel, s', ?_, hObs⟩⟩
      simpa [hs'] using self_mem_execBlockPath_nil s'
    · refine ⟨[block0], by simp [witnessPaths], ?_⟩
      refine ⟨hRel, s', ?_, hObs⟩
      simpa [hs'] using execBlock_mem_execBlockPath_singleton s

example : WitnessComplete region witnessPaths :=
  witnessComplete

example :
    ∀ s o,
      VexModelDenotesObs Relevant observe (lowerPathFamilySummaries witnessPaths) s o ↔
        region.DenotesObs s o := by
  exact extractedModel_of_witnessComplete region witnessPaths witnessComplete

end Instances.Examples.Tier8WitnessedSubsystem
