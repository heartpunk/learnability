import Instances.ISAs.VexAmd64

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Instances.Examples.VexLeaRdiPlus5Fixture

open VexISA

def bytes : List UInt8 := [0x48, 0x8d, 0x47, 0x05]

def block : Amd64Block :=
  mkAmd64Block [
      .wrTmp 2 (.get .rdi),
      .wrTmp 1 (.add64 (.tmp 2) (.const 0x5)),
      .put .rax (.tmp 1)
    ] 0x400004

def input : Amd64ConcreteState :=
  mkAmd64State
    0x0
    0x0
    0x10
    0x400000
    ByteMem.empty

def expected : Amd64ConcreteState :=
  mkAmd64State
    0x15
    0x0
    0x10
    0x400004
    ByteMem.empty

end Instances.Examples.VexLeaRdiPlus5Fixture
