import Instances.Examples.Tier0Increment
import Instances.ISAs.VexModelEq

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA

namespace Instances.Examples.Tier5ProgramTrace

abbrev Reg := Instances.Examples.ToyReg

/-- First fetched block: increment `r0`, advance IP to 1. -/
def block0 : Block Reg :=
  { stmts := [Stmt.put .r0 (.add64 (.get .r0) (.const 1))]
    ip_reg := .r1
    next := 1 }

/-- Second fetched block: increment `r0` by 2, advance IP to 2. -/
def block1 : Block Reg :=
  { stmts := [Stmt.put .r0 (.add64 (.get .r0) (.const 2))]
    ip_reg := .r1
    next := 2 }

def program : Program Reg where
  blocks
    | 0 => some block0
    | 1 => some block1
    | _ => none

def Relevant : ConcreteState Reg → Prop := fun _ => True

def observe (s : ConcreteState Reg) : UInt64 × UInt64 :=
  (s.read .r0, s.read .r1)

example : ExtractibleProgramTrace Relevant observe program .r1 := by
  exact extractibleProgramTrace_of_lowering Relevant observe program .r1

example : ExtractibleProgramStep Relevant observe program .r1 := by
  exact extractibleProgramStep_of_lowering Relevant observe program .r1

end Instances.Examples.Tier5ProgramTrace
