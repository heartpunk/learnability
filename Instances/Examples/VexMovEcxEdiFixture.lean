import Instances.ISAs.VexAmd64

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Instances.Examples.VexMovEcxEdiFixture

open VexISA

def bytes : List UInt8 := [0x89, 0xf9]

def block : Amd64Block :=
  mkAmd64Block [
      .wrTmp 2 (.get .rdi),
      .wrTmp 1 (.narrow32 (.tmp 2)),
      .wrTmp 0 (.zext64 (.tmp 1)),
      .put .rcx (.tmp 0)
    ] 0x400002

def input : Amd64ConcreteState :=
  mkAmd64StateCC
    0x0
    0xdeadbeefdeadbeef
    0x0
    0x0
    0x0
    0x0
    0x1122334455667788
    0x400000
    0x0
    0x0
    0x0
    0x0
    ByteMem.empty

def expected : Amd64ConcreteState :=
  mkAmd64StateCC
    0x0
    0x55667788
    0x0
    0x0
    0x0
    0x0
    0x1122334455667788
    0x400002
    0x0
    0x0
    0x0
    0x0
    ByteMem.empty

end Instances.Examples.VexMovEcxEdiFixture
