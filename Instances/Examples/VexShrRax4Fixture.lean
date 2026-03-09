import Instances.ISAs.VexAmd64

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Instances.Examples.VexShrRax4Fixture

open VexISA

def bytes : List UInt8 := [0x48, 0xc1, 0xe8, 0x04]

def block : Amd64Block :=
  mkAmd64Block [
      .wrTmp 0 (.get .rax),
      .wrTmp 3 (.shr64 (.tmp 0) (.const 0x4)),
      .wrTmp 7 (.shr64 (.tmp 0) (.const 0x3)),
      .put .cc_op (.const 0x24),
      .put .cc_dep1 (.tmp 3),
      .put .cc_dep2 (.tmp 7),
      .put .rax (.tmp 3)
    ] 0x400004

def input : Amd64ConcreteState :=
  mkAmd64StateCC
    0xfedcba9876543210
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
    0xfedcba987654321
    0x0
    0x0
    0x400004
    0x24
    0xfedcba987654321
    0x1fdb97530eca8642
    0x0
    ByteMem.empty

end Instances.Examples.VexShrRax4Fixture
