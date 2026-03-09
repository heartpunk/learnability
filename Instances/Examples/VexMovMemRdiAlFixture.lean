import Instances.ISAs.VexAmd64

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Instances.Examples.VexMovMemRdiAlFixture

open VexISA

def bytes : List UInt8 := [0x88, 0x07]

def block : Amd64Block :=
  mkAmd64Block [
      .wrTmp 0 (.get .rdi),
      .wrTmp 1 (.get .rax),
      .store .w8 (.tmp 0) (.tmp 1)
    ] 0x400002

def input : Amd64ConcreteState :=
  mkAmd64StateCC
    0x88
    0x0
    0x20
    0x400000
    0x0
    0x0
    0x0
    0x0
    ByteMem.empty

def expected : Amd64ConcreteState :=
  mkAmd64StateCC
    0x88
    0x0
    0x20
    0x400002
    0x0
    0x0
    0x0
    0x0
    (ByteMem.write64le ByteMem.empty 0x20 0x88)

end Instances.Examples.VexMovMemRdiAlFixture
