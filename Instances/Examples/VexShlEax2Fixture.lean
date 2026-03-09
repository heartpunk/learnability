import Instances.ISAs.VexAmd64

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Instances.Examples.VexShlEax2Fixture

open VexISA

def bytes : List UInt8 := [0xC1, 0xE0, 0x02]

def block : Amd64Block :=
  mkAmd64Block [
      .wrTmp 0 (.get .rax),
      .wrTmp 1 (.narrow32 (.tmp 0)),
      .wrTmp 2 (.shl32 (.tmp 1) (.const 0x2)),
      .put .cc_op (.const 0x1F),
      .wrTmp 3 (.zext64 (.tmp 1)),
      .put .cc_dep1 (.tmp 3),
      .wrTmp 4 (.zext64 (.tmp 2)),
      .put .cc_dep2 (.tmp 4),
      .wrTmp 5 (.zext64 (.tmp 2)),
      .put .rax (.tmp 5)
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
    0x1F
    0x1
    0x4
    0x0
    ByteMem.empty

end Instances.Examples.VexShlEax2Fixture
