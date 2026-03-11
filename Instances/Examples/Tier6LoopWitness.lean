import Instances.Examples.Tier0Increment
import Instances.ISAs.VexWitness
import Instances.ISAs.VexProofCompression

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA

namespace Instances.Examples.Tier6LoopWitness

abbrev Reg := Instances.Examples.ToyReg

abbrev block : Block Reg := Instances.Examples.block

def body : List (Block Reg) := [block]

def K : Nat := 0

def program : Program Reg where
  blocks := fun _ => none

def Relevant : ConcreteState Reg → Prop := fun _ => True

def observe (s : ConcreteState Reg) : UInt64 × UInt64 :=
  (s.read .r0, s.read .r1)

def loop : VexLoopSummary Reg where
  body := CompTree.assign (lowerBlockSub block)
  continues := .not .true
  exits := .true
  bodyEffect := execBlock block
  bodyEffect_spec := bodyEffect_spec_assign_lowerBlockSub block
  guard_partition := by
    intro s
    simp [vexSummaryISA, satisfiesSymPC, evalSymPC]

def spec : LoopRegionSpec Reg (UInt64 × UInt64) :=
  whileLoopRegionSpec program .r1 loop Relevant observe

private theorem hpath :
    ∀ n, ∀ s s',
      n ≤ K → s' ∈ execBlockPath (repeatBlockPath body n) s →
        boundedWhileBehavior (isa := vexSummaryISA Reg) loop K s s' := by
  intro n s s' hn hExec
  have hn0 : n = 0 := by
    have hn' : n <= 0 := by simpa [K] using hn
    exact Nat.eq_zero_of_le_zero hn'
  subst hn0
  have hs' : s' = s := by
    simpa [body, execBlockPath] using hExec
  subst s'
  refine ⟨0, le_rfl, rfl, ?_, ?_⟩
  · intro k hk
    exact (Nat.not_lt_zero _ hk).elim
  · simp [loop, vexSummaryISA, satisfiesSymPC, evalSymPC]

private theorem hsound : LoopWitnessSound spec body K := by
  exact whileLoopWitnessSound_of_boundedPathBehavior program .r1 loop Relevant observe body K hpath

private theorem hbound : WhileLoopUnrollBound program .r1 loop Relevant observe body K := by
  intro s o hDenotes
  rcases hDenotes with ⟨hRel, s', hWhile, hObs⟩
  rcases hWhile with ⟨n, hIter, hCont, hExit⟩
  have hn0 : n = 0 := by
    by_contra hne
    have hnpos : 0 < n := Nat.pos_of_ne_zero hne
    have hContinue : (vexSummaryISA Reg).satisfies s loop.continues := hCont 0 hnpos
    have : False := by
      simp [loop, vexSummaryISA, satisfiesSymPC, evalSymPC] at hContinue
    exact this.elim
  subst hn0
  have hs' : s' = s := by
    simpa [iterateBody] using hIter.symm
  subst s'
  refine ⟨[], nil_mem_boundedLoopWitness body K, ?_⟩
  exact ⟨hRel, s, by simp [execBlockPath], hObs⟩

example : LoopWitnessComplete spec body K := by
  exact loopWitnessComplete_of_sound_and_unrollBound spec body K hsound hbound

example : ∀ s o,
    VexModelDenotesObs Relevant observe
      (lowerPathFamilySummaries (boundedLoopWitness body K)) s o ↔
        spec.DenotesObs s o := by
  exact extractedLoopModel_of_witnessComplete spec body K
    (loopWitnessComplete_of_sound_and_unrollBound spec body K hsound hbound)

end Instances.Examples.Tier6LoopWitness
