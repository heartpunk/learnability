import Instances.ISAs.VexAmd64

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Instances.Examples.VexLeaRaxRdiPlusRcxPlus8Fixture

open VexISA

def bytes : List UInt8 := [0x48, 0x8d, 0x44, 0x0f, 0x08]

def block : Amd64Block :=
  mkAmd64Block [
      .wrTmp 3 (.get .rdi),
      .wrTmp 5 (.get .rcx),
      .wrTmp 2 (.add64 (.tmp 3) (.tmp 5)),
      .wrTmp 1 (.add64 (.tmp 2) (.const 0x8)),
      .put .rax (.tmp 1)
    ] 0x400005

def input : Amd64ConcreteState :=
  mkAmd64State
    0x0
    0x3
    0x10
    0x400000
    ByteMem.empty

def expected : Amd64ConcreteState :=
  mkAmd64State
    0x1b
    0x3
    0x10
    0x400005
    ByteMem.empty

end Instances.Examples.VexLeaRaxRdiPlusRcxPlus8Fixture
