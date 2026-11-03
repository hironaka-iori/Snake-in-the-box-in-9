import Recovered122G.LocalWindowUnsat.End35.Data23
import Recovered122G.LocalWindowUnsat.End35.Data24

/-! Kernel checks of segments 133-138 of `end35` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End35
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok133 : check start133 proof133 = true := by
  decide +kernel

theorem ok134 : check start134 proof134 = true := by
  decide +kernel

theorem ok135 : check start135 proof135 = true := by
  decide +kernel

theorem ok136 : check start136 proof136 = true := by
  decide +kernel

theorem ok137 : check start137 proof137 = true := by
  decide +kernel

theorem ok138 : andB (check start138 proof138) (cpOk (replay start138 proof138) start139) = true := by
  decide +kernel

end Snake9.LocalWindow.End35
