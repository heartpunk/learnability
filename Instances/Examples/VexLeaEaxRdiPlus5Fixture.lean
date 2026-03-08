import Instances.ISAs.VexAmd64

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Instances.Examples.VexLeaEaxRdiPlus5Fixture

open VexISA

def bytes : List UInt8 := [0x8d, 0x47, 0x05]

def block : Amd64Block :=
  mkAmd64Block [
      .wrTmp 2 (.get .rdi),
      .wrTmp 1 (.add64 (.tmp 2) (.const 0x5)),
      .wrTmp 4 (.low32 (.tmp 1)),
      .wrTmp 3 (.uext32 (.tmp 4)),
      .put .rax (.tmp 3)
    ] 0x400003

def input : Amd64ConcreteState :=
  mkAmd64State
    0xdeadbeefdeadbeef
    0x0
    0x1122334455667788
    0x400000
    ByteMem.empty

def expected : Amd64ConcreteState :=
  mkAmd64State
    0x5566778d
    0x0
    0x1122334455667788
    0x400003
    ByteMem.empty

end Instances.Examples.VexLeaEaxRdiPlus5Fixture
