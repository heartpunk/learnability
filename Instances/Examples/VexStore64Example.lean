import Instances.ISAs.VexLoweringCorrectness
import Instances.ISAs.VexAmd64

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA

def storeBlock : Amd64Block :=
  mkAmd64Block [
      .store64 (.get .rdi) (.get .rax)
    ] 0x400003

def storeInput : Amd64ConcreteState :=
  mkAmd64State
    0x1122334455667788
    0x0
    0x20
    0x400000
    (ByteMem.write64le ByteMem.empty 0x20 0x0)

def storeExpected : Amd64ConcreteState :=
  mkAmd64State
    0x1122334455667788
    0x0
    0x20
    0x400003
    (ByteMem.write64le ByteMem.empty 0x20 0x1122334455667788)

example : execBlock storeBlock storeInput = storeExpected := by
  native_decide

example : Summary.apply (lowerBlock storeBlock) storeInput = storeExpected := by
  rw [VexISA.lowerBlock_sound]
  native_decide
