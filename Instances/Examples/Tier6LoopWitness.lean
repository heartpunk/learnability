import Instances.Examples.Tier0Increment
import Instances.ISAs.VexWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA

namespace Instances.Examples.Tier6LoopWitness

abbrev Reg := Instances.Examples.ToyReg

def body : List (Block Reg) := [Instances.Examples.block]

def K : Nat := 2

def program : Program Reg where
  blocks := fun _ => none

def Relevant : ConcreteState Reg → Prop := fun _ => True

def observe (s : ConcreteState Reg) : UInt64 × UInt64 :=
  (s.read .r0, s.read .r1)

/-- Extensional loop region chosen to match the bounded witness exactly. This keeps the
example focused on the loop-witness theorem stack itself. -/
def spec : LoopRegionSpec Reg (UInt64 × UInt64) where
  program := program
  ip_reg := .r1
  Relevant := Relevant
  observe := observe
  DenotesObs := fun s o =>
    ExecPathFamilyDenotesObs Relevant observe (boundedLoopWitness body K) s o

private theorem hsound : LoopWitnessSound spec body K := by
  intro s o h
  exact h

private theorem hbound : LoopUnrollBound spec body K := by
  intro s o h
  exact h

example : LoopWitnessComplete spec body K := by
  exact loopWitnessComplete_of_sound_and_unrollBound spec body K hsound hbound

example : ∀ s o,
    VexModelDenotesObs Relevant observe
      (lowerPathFamilySummaries (boundedLoopWitness body K)) s o ↔
        spec.DenotesObs s o := by
  exact extractedLoopModel_of_witnessComplete spec body K
    (loopWitnessComplete_of_sound_and_unrollBound spec body K hsound hbound)

end Instances.Examples.Tier6LoopWitness
