import Instances.ISAs.VexAmd64

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Instances.Examples.VexMovMemRdiRaxFixture

open VexISA

def bytes : List UInt8 := [0x48, 0x89, 0x07]

def block : Amd64Block :=
  mkAmd64Block [
      .wrTmp 0 (.get .rdi),
      .wrTmp 1 (.get .rax),
      .store64 (.tmp 0) (.tmp 1)
    ] 0x400003

def input : Amd64ConcreteState :=
  mkAmd64State
    0x1122334455667788
    0x0
    0x20
    0x400000
    (ByteMem.write64le ByteMem.empty 0x20 0xdeadbeefcafebabe)

def expected : Amd64ConcreteState :=
  mkAmd64State
    0x1122334455667788
    0x0
    0x20
    0x400003
    (ByteMem.write64le ByteMem.empty 0x20 0x1122334455667788)

end Instances.Examples.VexMovMemRdiRaxFixture
