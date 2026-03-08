import Instances.ISAs.VexAmd64

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Instances.Examples.VexMovRdiRcxFixture

open VexISA

def bytes : List UInt8 := [0x48, 0x89, 0xcf]

def block : Amd64Block :=
  mkAmd64Block [
      .wrTmp 0 (.get .rcx),
      .put .rdi (.tmp 0)
    ] 0x400003

def input : Amd64ConcreteState :=
  mkAmd64StateCC
    0x0
    0x10
    0x0
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
    0x10
    0x400003
    0x0
    0x0
    0x0
    0x0
    ByteMem.empty

end Instances.Examples.VexMovRdiRcxFixture
