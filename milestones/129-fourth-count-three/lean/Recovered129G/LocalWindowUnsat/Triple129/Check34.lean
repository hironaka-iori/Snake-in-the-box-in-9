import Recovered129G.LocalWindowUnsat.Triple129.Data34
import Recovered129G.LocalWindowUnsat.Triple129.Data35

/-! Kernel checks of segments 133-136 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok133 : check start133 proof133 = true := by
  decide +kernel

theorem ok134 : check start134 proof134 = true := by
  decide +kernel

theorem ok135 : check start135 proof135 = true := by
  decide +kernel

theorem ok136 : andB (check start136 proof136) (cpOk (replay start136 proof136) start137) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
