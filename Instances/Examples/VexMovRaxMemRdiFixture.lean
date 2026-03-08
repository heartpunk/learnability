import Instances.ISAs.VexISA

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Instances.Examples.VexMovRaxMemRdiFixture

open VexISA

def bytes : List UInt8 := [0x48, 0x8b, 0x07]

def block : Block :=
  { stmts := [
      .wrTmp 0 (.get .rdi),
      .wrTmp 1 (.load64 (.tmp 0)),
      .put .rax (.tmp 1)
    ],
    next := 0x400003 }

def input : ConcreteState :=
  { rax := 0x0,
    rcx := 0x0,
    rdi := 0x20,
    rip := 0x400000,
    mem := (ByteMem.write64le ByteMem.empty 0x20 0x1122334455667788) }

def expected : ConcreteState :=
  { rax := 0x1122334455667788,
    rcx := 0x0,
    rdi := 0x20,
    rip := 0x400003,
    mem := (ByteMem.write64le ByteMem.empty 0x20 0x1122334455667788) }

end Instances.Examples.VexMovRaxMemRdiFixture
