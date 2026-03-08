import Mathlib.Data.Finset.Basic
import Instances.ISAs.VexLoweringCorrectness
import Instances.Examples.VexJzOnlyTakenFixture
import Instances.Examples.VexJzOnlyFallthroughFixture

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA

namespace Instances.Examples

example :
    execBlockSuccs VexJzOnlyTakenFixture.block VexJzOnlyTakenFixture.input =
      ({VexJzOnlyTakenFixture.expected} : Finset Amd64ConcreteState) := by
  native_decide

example (summary : Summary Amd64Reg)
    (hMem : summary ∈ lowerBlockSummaries VexJzOnlyTakenFixture.block)
    (hEnabled : Summary.enabled summary VexJzOnlyTakenFixture.input) :
    Summary.apply summary VexJzOnlyTakenFixture.input = VexJzOnlyTakenFixture.expected := by
  exact lowerBlockSummaries_complete_eq_of_unique
    VexJzOnlyTakenFixture.block
    VexJzOnlyTakenFixture.input
    VexJzOnlyTakenFixture.expected
    summary
    (by native_decide)
    hMem
    hEnabled

example :
    execBlockSuccs VexJzOnlyFallthroughFixture.block VexJzOnlyFallthroughFixture.input =
      ({VexJzOnlyFallthroughFixture.expected} : Finset Amd64ConcreteState) := by
  native_decide

example (summary : Summary Amd64Reg)
    (hMem : summary ∈ lowerBlockSummaries VexJzOnlyFallthroughFixture.block)
    (hEnabled : Summary.enabled summary VexJzOnlyFallthroughFixture.input) :
    Summary.apply summary VexJzOnlyFallthroughFixture.input = VexJzOnlyFallthroughFixture.expected := by
  exact lowerBlockSummaries_complete_eq_of_unique
    VexJzOnlyFallthroughFixture.block
    VexJzOnlyFallthroughFixture.input
    VexJzOnlyFallthroughFixture.expected
    summary
    (by native_decide)
    hMem
    hEnabled

end Instances.Examples
