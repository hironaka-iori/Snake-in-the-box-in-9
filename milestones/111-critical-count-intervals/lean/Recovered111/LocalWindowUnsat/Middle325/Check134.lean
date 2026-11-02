import Recovered111.LocalWindowUnsat.Middle325.Data133
import Recovered111.LocalWindowUnsat.Middle325.Data134

/-! Kernel checks of segments 134-134 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok134 : andB (check start134 proof134) (cpOk (replay start134 proof134) start135) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
