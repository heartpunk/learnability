import Instances.ISAs.VexAmd64

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Instances.Examples.VexMovRaxMemRdiFixture

open VexISA

def bytes : List UInt8 := [0x48, 0x8b, 0x07]

def block : Amd64Block :=
  mkAmd64Block [
      .wrTmp 0 (.get .rdi),
      .wrTmp 1 (.load .w64 (.tmp 0)),
      .put .rax (.tmp 1)
    ] 0x400003

def input : Amd64ConcreteState :=
  mkAmd64StateCC
    0x0
    0x0
    0x20
    0x400000
    0x0
    0x0
    0x0
    0x0
    (ByteMem.write64le ByteMem.empty 0x20 0x1122334455667788)

def expected : Amd64ConcreteState :=
  mkAmd64StateCC
    0x1122334455667788
    0x0
    0x20
    0x400003
    0x0
    0x0
    0x0
    0x0
    (ByteMem.write64le ByteMem.empty 0x20 0x1122334455667788)

end Instances.Examples.VexMovRaxMemRdiFixture
