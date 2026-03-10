import Instances.ISAs.VexAmd64

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Instances.Examples.VexJzOnlyTakenFixture

open VexISA

def bytes : List UInt8 := [0x74, 0x02]

def block : Amd64Block :=
  mkAmd64Block [
      .wrTmp 1 (.get .cc_op),
      .wrTmp 2 (.get .cc_dep1),
      .wrTmp 3 (.get .cc_dep2),
      .wrTmp 4 (.get .cc_ndep),
      .exit (.amd64CalculateCondition 0x4 (.tmp 1) (.tmp 2) (.tmp 3) (.tmp 4)) 0x400004
    ] 0x400002

def input : Amd64ConcreteState :=
  mkAmd64StateCC
    0x0
    0x0
    0x0
    0x0
    0x0
    0x0
    0x0
    0x400000
    0x3
    0xffffffff
    0x1
    0x0
    ByteMem.empty

def expected : Amd64ConcreteState :=
  mkAmd64StateCC
    0x0
    0x0
    0x0
    0x0
    0x0
    0x0
    0x0
    0x400004
    0x3
    0xffffffff
    0x1
    0x0
    ByteMem.empty

end Instances.Examples.VexJzOnlyTakenFixture
