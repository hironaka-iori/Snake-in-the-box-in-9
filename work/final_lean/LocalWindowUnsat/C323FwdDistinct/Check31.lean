import LocalWindowUnsat.C323FwdDistinct.Data124

/-! Kernel checks of segments 121-124 of `323_fwd_distinct` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C323FwdDistinct
open Snake9.Lrat

theorem ok121 : check start121 proof121 = true := by
  decide +kernel

theorem ok122 : check start122 proof122 = true := by
  decide +kernel

theorem ok123 : andB (check start123 proof123) (cpOk (replay start123 proof123) cp124) = true := by
  decide +kernel

theorem ok124 : check start124 proof124 = true := by
  decide +kernel

end Snake9.LocalWindow.C323FwdDistinct
