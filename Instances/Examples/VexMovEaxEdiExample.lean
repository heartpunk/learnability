import Instances.ISAs.VexLoweringCorrectness
import Instances.Examples.VexMovEaxEdiFixture

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA
open Instances.Examples.VexMovEaxEdiFixture

example : execBlock block input = expected := by
  native_decide

example : Summary.apply (lowerBlock block) input = expected := by
  rw [VexISA.lowerBlock_sound]
  native_decide
