import Instances.ISAs.VexAmd64

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Instances.Examples.VexCmpRaxRdiJbFallthroughFixture

open VexISA

def bytes : List UInt8 := [0x48, 0x39, 0xf8, 0x72, 0x02]

def block : Amd64Block :=
  mkAmd64Block [
      .wrTmp 2 (.get .rax),
      .wrTmp 1 (.get .rdi),
      .put .cc_op (.const 0x8),
      .put .cc_dep1 (.tmp 2),
      .put .cc_dep2 (.tmp 1),
      .put .rip (.const 0x400003),
      .exit (.lt64 (.tmp 2) (.tmp 1)) 0x400007
    ] 0x400005

def input : Amd64ConcreteState :=
  mkAmd64StateCC
    0x3
    0x0
    0x3
    0x400000
    0x0
    0x0
    0x0
    0x0
    ByteMem.empty

def expected : Amd64ConcreteState :=
  mkAmd64StateCC
    0x3
    0x0
    0x3
    0x400005
    0x8
    0x3
    0x3
    0x0
    ByteMem.empty

end Instances.Examples.VexCmpRaxRdiJbFallthroughFixture
