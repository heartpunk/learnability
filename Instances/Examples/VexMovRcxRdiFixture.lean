import Instances.ISAs.VexAmd64

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Instances.Examples.VexMovRcxRdiFixture

open VexISA

def bytes : List UInt8 := [0x48, 0x89, 0xf9]

def block : Amd64Block :=
  mkAmd64Block [
      .wrTmp 0 (.get .rdi),
      .put .rcx (.tmp 0)
    ] 0x400003

def input : Amd64ConcreteState :=
  mkAmd64StateCC
    0x0
    0x0
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
    0x0
    0x10
    0x0
    0x0
    0x0
    0x0
    0x10
    0x400003
    0x0
    0x0
    0x0
    0x0
    ByteMem.empty

end Instances.Examples.VexMovRcxRdiFixture
