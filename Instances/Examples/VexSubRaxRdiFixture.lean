import Instances.ISAs.VexAmd64

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Instances.Examples.VexSubRaxRdiFixture

open VexISA

def bytes : List UInt8 := [0x48, 0x29, 0xf8]

def block : Amd64Block :=
  mkAmd64Block [
      .wrTmp 2 (.get .rax),
      .wrTmp 1 (.get .rdi),
      .wrTmp 0 (.sub64 (.tmp 2) (.tmp 1)),
      .put .cc_op (.const 0x8),
      .put .cc_dep1 (.tmp 2),
      .put .cc_dep2 (.tmp 1),
      .put .rax (.tmp 0)
    ] 0x400003

def input : Amd64ConcreteState :=
  mkAmd64StateCC
    0x10
    0x0
    0x0
    0x0
    0x0
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
    0xd
    0x0
    0x0
    0x0
    0x0
    0x0
    0x3
    0x400003
    0x8
    0x10
    0x3
    0x0
    ByteMem.empty

end Instances.Examples.VexSubRaxRdiFixture
