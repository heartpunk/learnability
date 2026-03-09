import Mathlib.Data.Finset.Basic
import Instances.ISAs.VexLoweringCorrectness
import Instances.Examples.VexCmpRaxRdiJbeTakenFixture
import Instances.Examples.VexCmpRaxRdiJbeFallthroughFixture

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA

namespace Instances.Examples

example :
    execBlockSuccs VexCmpRaxRdiJbeTakenFixture.block VexCmpRaxRdiJbeTakenFixture.input =
      ({VexCmpRaxRdiJbeTakenFixture.expected} : Finset Amd64ConcreteState) := by
  native_decide

example (summary : Summary Amd64Reg)
    (hMem : summary ∈ lowerBlockSummaries VexCmpRaxRdiJbeTakenFixture.block)
    (hEnabled : Summary.enabled summary VexCmpRaxRdiJbeTakenFixture.input) :
    Summary.apply summary VexCmpRaxRdiJbeTakenFixture.input =
      VexCmpRaxRdiJbeTakenFixture.expected := by
  exact lowerBlockSummaries_complete_eq_of_unique
    VexCmpRaxRdiJbeTakenFixture.block
    VexCmpRaxRdiJbeTakenFixture.input
    VexCmpRaxRdiJbeTakenFixture.expected
    summary
    (by native_decide)
    hMem
    hEnabled

example :
    execBlockSuccs VexCmpRaxRdiJbeFallthroughFixture.block VexCmpRaxRdiJbeFallthroughFixture.input =
      ({VexCmpRaxRdiJbeFallthroughFixture.expected} : Finset Amd64ConcreteState) := by
  native_decide

example (summary : Summary Amd64Reg)
    (hMem : summary ∈ lowerBlockSummaries VexCmpRaxRdiJbeFallthroughFixture.block)
    (hEnabled : Summary.enabled summary VexCmpRaxRdiJbeFallthroughFixture.input) :
    Summary.apply summary VexCmpRaxRdiJbeFallthroughFixture.input =
      VexCmpRaxRdiJbeFallthroughFixture.expected := by
  exact lowerBlockSummaries_complete_eq_of_unique
    VexCmpRaxRdiJbeFallthroughFixture.block
    VexCmpRaxRdiJbeFallthroughFixture.input
    VexCmpRaxRdiJbeFallthroughFixture.expected
    summary
    (by native_decide)
    hMem
    hEnabled

end Instances.Examples
