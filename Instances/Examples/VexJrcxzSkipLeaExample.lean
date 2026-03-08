import Instances.ISAs.VexLoweringCorrectness
import Instances.Examples.VexJrcxzSkipLeaTakenFixture
import Instances.Examples.VexJrcxzSkipLeaFallthroughFixture

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA

namespace Instances.Examples.VexJrcxzSkipLeaTakenFixture

example : expected ∈ execBlockSuccs block input := by
  decide

example :
    ∃ summary ∈ lowerBlockSummaries block,
      Summary.enabled summary input ∧ Summary.apply summary input = expected := by
  exact lowerBlockSummaries_sound block input expected (by decide)

example (summary : Summary)
    (hMem : summary ∈ lowerBlockSummaries block)
    (hEnabled : Summary.enabled summary input) :
    Summary.apply summary input = expected := by
  have hSucc := lowerBlockSummaries_complete block input summary hMem hEnabled
  simpa [block, input, expected, execBlockSuccs, execStmtsSuccs, evalCond, evalExpr] using hSucc

end Instances.Examples.VexJrcxzSkipLeaTakenFixture

namespace Instances.Examples.VexJrcxzSkipLeaFallthroughFixture

example : expected ∈ execBlockSuccs block input := by
  decide

example :
    ∃ summary ∈ lowerBlockSummaries block,
      Summary.enabled summary input ∧ Summary.apply summary input = expected := by
  exact lowerBlockSummaries_sound block input expected (by decide)

example (summary : Summary)
    (hMem : summary ∈ lowerBlockSummaries block)
    (hEnabled : Summary.enabled summary input) :
    Summary.apply summary input = expected := by
  have hSucc := lowerBlockSummaries_complete block input summary hMem hEnabled
  simpa [block, input, expected, execBlockSuccs, execStmtsSuccs, evalCond, evalExpr] using hSucc

end Instances.Examples.VexJrcxzSkipLeaFallthroughFixture
