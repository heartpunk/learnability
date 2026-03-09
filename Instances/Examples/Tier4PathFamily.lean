import Instances.Examples.Tier0Increment
import Instances.Examples.Tier1Branch
import Instances.ISAs.VexModelEq

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA

namespace Instances.Examples.Tier4PathFamily

abbrev Reg := Instances.Examples.ToyReg

def pathInc : List (Block Reg) := [Instances.Examples.block]
def pathBranch : List (Block Reg) := [Instances.Examples.Tier1Branch.block]

def paths : Finset (List (Block Reg)) := {pathInc, pathBranch}

def Relevant : ConcreteState Reg → Prop := fun _ => True

def observe (s : ConcreteState Reg) : UInt64 × UInt64 :=
  (s.read .r0, s.read .r1)

example : ExtractiblePathFamilyModel Relevant observe paths := by
  exact lowerPathFamilySummaries_denotesObs_iff_execPathFamily Relevant observe paths

end Instances.Examples.Tier4PathFamily
