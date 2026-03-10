import Instances.ISAs.VexAmd64

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Instances.Examples.VexAndRaxRdiFixture

open VexISA

def bytes : List UInt8 := [0x48, 0x21, 0xf8]

def block : Amd64Block :=
  mkAmd64Block [
      .wrTmp 2 (.get .rax),
      .wrTmp 1 (.get .rdi),
      .wrTmp 0 (.and64 (.tmp 2) (.tmp 1)),
      .put .cc_op (.const 0x14),
      .put .cc_dep1 (.tmp 0),
      .put .cc_dep2 (.const 0x0),
      .put .rax (.tmp 0)
    ] 0x400003

def input : Amd64ConcreteState :=
  mkAmd64StateCC
    0xff00ff00aa55aa55
    0x0
    0x0
    0x0
    0x0
    0x0
    0xf0f0f0f12345678
    0x400000
    0x0
    0x0
    0x0
    0x0
    ByteMem.empty

def expected : Amd64ConcreteState :=
  mkAmd64StateCC
    0xf000f0002140250
    0x0
    0x0
    0x0
    0x0
    0x0
    0xf0f0f0f12345678
    0x400003
    0x14
    0xf000f0002140250
    0x0
    0x0
    ByteMem.empty

end Instances.Examples.VexAndRaxRdiFixture
