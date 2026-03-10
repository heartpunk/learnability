import Instances.ISAs.VexAmd64

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Instances.Examples.VexMovslqRaxEdiFixture

open VexISA

def bytes : List UInt8 := [0x48, 0x63, 0xc7]

def block : Amd64Block :=
  mkAmd64Block [
      .wrTmp 2 (.get .rdi),
      .wrTmp 1 (.narrow32 (.tmp 2)),
      .wrTmp 0 (.sext32to64 (.tmp 1)),
      .put .rax (.tmp 0)
    ] 0x400003

def input : Amd64ConcreteState :=
  mkAmd64StateCC
    0x0
    0x0
    0x0
    0x0
    0x0
    0x0
    0x12345678ffffff80
    0x400000
    0x0
    0x0
    0x0
    0x0
    ByteMem.empty

def expected : Amd64ConcreteState :=
  mkAmd64StateCC
    0xffffffffffffff80
    0x0
    0x0
    0x0
    0x0
    0x0
    0x12345678ffffff80
    0x400003
    0x0
    0x0
    0x0
    0x0
    ByteMem.empty

end Instances.Examples.VexMovslqRaxEdiFixture
