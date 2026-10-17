import LocalWindowUnsat.C323FwdDistinct.Data112

/-! Kernel checks of segments 109-112 of `323_fwd_distinct` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C323FwdDistinct
open Snake9.Lrat

theorem ok109 : check start109 proof109 = true := by
  decide +kernel

theorem ok110 : check start110 proof110 = true := by
  decide +kernel

theorem ok111 : andB (check start111 proof111) (cpOk (replay start111 proof111) cp112) = true := by
  decide +kernel

theorem ok112 : check start112 proof112 = true := by
  decide +kernel

end Snake9.LocalWindow.C323FwdDistinct
