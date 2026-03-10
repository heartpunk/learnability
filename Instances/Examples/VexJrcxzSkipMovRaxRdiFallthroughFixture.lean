import Instances.ISAs.VexAmd64

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Instances.Examples.VexJrcxzSkipMovRaxRdiFallthroughFixture

open VexISA

def bytes : List UInt8 := [0xe3, 0x03, 0x48, 0x89, 0xf8]

def block : Amd64Block :=
  mkAmd64Block [
      .wrTmp 1 (.get .rcx),
      .exit (.eq64 (.tmp 1) (.const 0x0)) 0x400005,
      .wrTmp 2 (.get .rdi),
      .put .rax (.tmp 2)
    ] 0x400005

def input : Amd64ConcreteState :=
  mkAmd64StateCC
    0x0
    0x1
    0x0
    0x0
    0x0
    0x0
    0x10
    0x400000
    0x0
    0x0
    0x0
    0x0
    ByteMem.empty

def expected : Amd64ConcreteState :=
  mkAmd64StateCC
    0x10
    0x1
    0x0
    0x0
    0x0
    0x0
    0x10
    0x400005
    0x0
    0x0
    0x0
    0x0
    ByteMem.empty

end Instances.Examples.VexJrcxzSkipMovRaxRdiFallthroughFixture
