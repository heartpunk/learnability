import Mathlib.Data.Finset.Basic
import Instances.ISAs.VexLoweringCorrectness
import Instances.Examples.VexCmpRaxRdiJbTakenFixture
import Instances.Examples.VexCmpRaxRdiJbFallthroughFixture

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA

namespace Instances.Examples

example :
    execBlockSuccs VexCmpRaxRdiJbTakenFixture.block VexCmpRaxRdiJbTakenFixture.input =
      ({VexCmpRaxRdiJbTakenFixture.expected} : Finset Amd64ConcreteState) := by
  native_decide

example (summary : Summary Amd64Reg)
    (hMem : summary ∈ lowerBlockSummaries VexCmpRaxRdiJbTakenFixture.block)
    (hEnabled : Summary.enabled summary VexCmpRaxRdiJbTakenFixture.input) :
    Summary.apply summary VexCmpRaxRdiJbTakenFixture.input = VexCmpRaxRdiJbTakenFixture.expected := by
  exact lowerBlockSummaries_complete_eq_of_unique
    VexCmpRaxRdiJbTakenFixture.block
    VexCmpRaxRdiJbTakenFixture.input
    VexCmpRaxRdiJbTakenFixture.expected
    summary
    (by native_decide)
    hMem
    hEnabled

example :
    execBlockSuccs VexCmpRaxRdiJbFallthroughFixture.block VexCmpRaxRdiJbFallthroughFixture.input =
      ({VexCmpRaxRdiJbFallthroughFixture.expected} : Finset Amd64ConcreteState) := by
  native_decide

example (summary : Summary Amd64Reg)
    (hMem : summary ∈ lowerBlockSummaries VexCmpRaxRdiJbFallthroughFixture.block)
    (hEnabled : Summary.enabled summary VexCmpRaxRdiJbFallthroughFixture.input) :
    Summary.apply summary VexCmpRaxRdiJbFallthroughFixture.input =
      VexCmpRaxRdiJbFallthroughFixture.expected := by
  exact lowerBlockSummaries_complete_eq_of_unique
    VexCmpRaxRdiJbFallthroughFixture.block
    VexCmpRaxRdiJbFallthroughFixture.input
    VexCmpRaxRdiJbFallthroughFixture.expected
    summary
    (by native_decide)
    hMem
    hEnabled

end Instances.Examples
