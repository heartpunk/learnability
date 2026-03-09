import Instances.ISAs.VexAmd64

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Instances.Examples.VexMovzxEaxMemRdiFixture

open VexISA

def bytes : List UInt8 := [0x0f, 0xb7, 0x07]

def block : Amd64Block :=
  mkAmd64Block [
      .wrTmp 0 (.get .rdi),
      .wrTmp 3 (.load .w16 (.tmp 0)),
      .wrTmp 2 (.tmp 3),
      .wrTmp 1 (.zext64 (.tmp 2)),
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
    0x7788
    0x0
    0x20
    0x400003
    0x0
    0x0
    0x0
    0x0
    (ByteMem.write64le ByteMem.empty 0x20 0x1122334455667788)

end Instances.Examples.VexMovzxEaxMemRdiFixture
