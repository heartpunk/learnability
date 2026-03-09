import Instances.ISAs.VexAmd64

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Instances.Examples.VexShlEax2Fixture

open VexISA

def bytes : List UInt8 := [0xc1, 0xe0, 0x02]

def block : Amd64Block :=
  mkAmd64Block [
      .wrTmp 8 (.get .rax),
      .wrTmp 7 (.narrow32 (.tmp 8)),
      .wrTmp 9 (.zext64 (.tmp 7)),
      .wrTmp 3 (.shl64 (.tmp 9) (.const 0x2)),
      .wrTmp 10 (.shl64 (.tmp 9) (.const 0x1)),
      .put .cc_op (.const 0x1f),
      .put .cc_dep1 (.tmp 3),
      .put .cc_dep2 (.tmp 10),
      .wrTmp 19 (.narrow32 (.tmp 3)),
      .wrTmp 20 (.zext64 (.tmp 19)),
      .put .rax (.tmp 20)
    ] 0x400003

def input : Amd64ConcreteState :=
  mkAmd64StateCC
    0x1
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
    0x4
    0x0
    0x0
    0x400003
    0x1f
    0x4
    0x2
    0x0
    ByteMem.empty

end Instances.Examples.VexShlEax2Fixture
