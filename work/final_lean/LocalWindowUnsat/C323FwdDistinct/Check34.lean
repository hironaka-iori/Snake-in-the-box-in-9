import LocalWindowUnsat.C323FwdDistinct.Data136

/-! Kernel checks of segments 133-136 of `323_fwd_distinct` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C323FwdDistinct
open Snake9.Lrat

theorem ok133 : check start133 proof133 = true := by
  decide +kernel

theorem ok134 : check start134 proof134 = true := by
  decide +kernel

theorem ok135 : andB (check start135 proof135) (cpOk (replay start135 proof135) cp136) = true := by
  decide +kernel

theorem ok136 : check start136 proof136 = true := by
  decide +kernel

end Snake9.LocalWindow.C323FwdDistinct
