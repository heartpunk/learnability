import Instances.ISAs.VexAmd64

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Instances.Examples.VexLeaRaxRdiFixture

open VexISA

def bytes : List UInt8 := [0x48, 0x8d, 0x07]

def block : Amd64Block :=
  mkAmd64Block [
      .wrTmp 0 (.get .rdi),
      .put .rax (.tmp 0)
    ] 0x400003

def input : Amd64ConcreteState :=
  mkAmd64State
    0x0
    0x0
    0x10
    0x400000
    ByteMem.empty

def expected : Amd64ConcreteState :=
  mkAmd64State
    0x10
    0x0
    0x10
    0x400003
    ByteMem.empty

end Instances.Examples.VexLeaRaxRdiFixture
