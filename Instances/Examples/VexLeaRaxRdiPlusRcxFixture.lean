import Instances.ISAs.VexAmd64

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Instances.Examples.VexLeaRaxRdiPlusRcxFixture

open VexISA

def bytes : List UInt8 := [0x48, 0x8d, 0x04, 0x0f]

def block : Amd64Block :=
  mkAmd64Block [
      .wrTmp 2 (.get .rdi),
      .wrTmp 4 (.get .rcx),
      .wrTmp 1 (.add64 (.tmp 2) (.tmp 4)),
      .put .rax (.tmp 1)
    ] 0x400004

def input : Amd64ConcreteState :=
  mkAmd64StateCC
    0x0
    0x3
    0x10
    0x400000
    0x0
    0x0
    0x0
    0x0
    ByteMem.empty

def expected : Amd64ConcreteState :=
  mkAmd64StateCC
    0x13
    0x3
    0x10
    0x400004
    0x0
    0x0
    0x0
    0x0
    ByteMem.empty

end Instances.Examples.VexLeaRaxRdiPlusRcxFixture
