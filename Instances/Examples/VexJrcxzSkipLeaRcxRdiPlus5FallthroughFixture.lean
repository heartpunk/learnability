import Instances.ISAs.VexAmd64

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Instances.Examples.VexJrcxzSkipLeaRcxRdiPlus5FallthroughFixture

open VexISA

def bytes : List UInt8 := [0xe3, 0x04, 0x48, 0x8d, 0x4f, 0x05]

def block : Amd64Block :=
  mkAmd64Block [
      .wrTmp 2 (.get .rcx),
      .exit (.eq64 (.tmp 2) (.const 0x0)) 0x400006,
      .wrTmp 4 (.get .rdi),
      .wrTmp 3 (.add64 (.tmp 4) (.const 0x5)),
      .put .rcx (.tmp 3)
    ] 0x400006

def input : Amd64ConcreteState :=
  mkAmd64State
    0x0
    0x1
    0x10
    0x400000
    ByteMem.empty

def expected : Amd64ConcreteState :=
  mkAmd64State
    0x0
    0x15
    0x10
    0x400006
    ByteMem.empty

end Instances.Examples.VexJrcxzSkipLeaRcxRdiPlus5FallthroughFixture
