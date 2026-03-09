import Instances.ISAs.VexAmd64

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Instances.Examples.VexSubEaxEdiFixture

open VexISA

def bytes : List UInt8 := [0x29, 0xf8]

def block : Amd64Block :=
  mkAmd64Block [
      .wrTmp 4 (.get .rax),
      .wrTmp 3 (.narrow32 (.tmp 4)),
      .wrTmp 6 (.get .rdi),
      .wrTmp 5 (.narrow32 (.tmp 6)),
      .wrTmp 0 (.sub32 (.tmp 3) (.tmp 5)),
      .put .cc_op (.const 0x7),
      .wrTmp 7 (.zext64 (.tmp 3)),
      .put .cc_dep1 (.tmp 7),
      .wrTmp 8 (.zext64 (.tmp 5)),
      .put .cc_dep2 (.tmp 8),
      .wrTmp 9 (.zext64 (.tmp 0)),
      .put .rax (.tmp 9)
    ] 0x400002

def input : Amd64ConcreteState :=
  mkAmd64StateCC
    0x100000002
    0x0
    0x3
    0x400000
    0x0
    0x0
    0x0
    0x0
    ByteMem.empty

def expected : Amd64ConcreteState :=
  mkAmd64StateCC
    0xffffffff
    0x0
    0x3
    0x400002
    0x7
    0x2
    0x3
    0x0
    ByteMem.empty

end Instances.Examples.VexSubEaxEdiFixture
