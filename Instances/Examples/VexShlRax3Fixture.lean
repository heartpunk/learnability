import Instances.ISAs.VexAmd64

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Instances.Examples.VexShlRax3Fixture

open VexISA

def bytes : List UInt8 := [0x48, 0xc1, 0xe0, 0x03]

def block : Amd64Block :=
  mkAmd64Block [
      .wrTmp 0 (.get .rax),
      .wrTmp 3 (.shl64 (.tmp 0) (.const 0x3)),
      .wrTmp 7 (.shl64 (.tmp 0) (.const 0x2)),
      .put .cc_op (.const 0x20),
      .put .cc_dep1 (.tmp 3),
      .put .cc_dep2 (.tmp 7),
      .put .rax (.tmp 3)
    ] 0x400004

def input : Amd64ConcreteState :=
  mkAmd64StateCC
    0x1122334455667788
    0x0
    0x0
    0x0
    0x0
    0x0
    0x0
    0x400000
    0x0
    0x0
    0x0
    0x0
    ByteMem.empty

def expected : Amd64ConcreteState :=
  mkAmd64StateCC
    0x89119a22ab33bc40
    0x0
    0x0
    0x0
    0x0
    0x0
    0x0
    0x400004
    0x20
    0x89119a22ab33bc40
    0x4488cd115599de20
    0x0
    ByteMem.empty

end Instances.Examples.VexShlRax3Fixture
