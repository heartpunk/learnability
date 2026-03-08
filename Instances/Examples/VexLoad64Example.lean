import Instances.ISAs.VexLoweringCorrectness
import Instances.ISAs.VexAmd64

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA

def loadBlock : Amd64Block :=
  mkAmd64Block [
      .wrTmp 0 (.load64 (.get .rdi)),
      .put .rax (.tmp 0)
    ] 0x400004

def loadInput : Amd64ConcreteState :=
  mkAmd64State
    0x0
    0x0
    0x20
    0x400000
    (ByteMem.write64le ByteMem.empty 0x20 0x1122334455667788)

def loadExpected : Amd64ConcreteState :=
  mkAmd64State
    0x1122334455667788
    0x0
    0x20
    0x400004
    (ByteMem.write64le ByteMem.empty 0x20 0x1122334455667788)

example : execBlock loadBlock loadInput = loadExpected := by
  native_decide

example : Summary.apply (lowerBlock loadBlock) loadInput = loadExpected := by
  rw [VexISA.lowerBlock_sound]
  native_decide
