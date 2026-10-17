import LocalWindowUnsat.C323FwdDistinct.Data168

/-! Kernel checks of segments 165-168 of `323_fwd_distinct` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C323FwdDistinct
open Snake9.Lrat

theorem ok165 : andB (check start165 proof165) (cpOk (replay start165 proof165) cp166) = true := by
  decide +kernel

theorem ok166 : check start166 proof166 = true := by
  decide +kernel

theorem ok167 : check start167 proof167 = true := by
  decide +kernel

theorem ok168 : andB (check start168 proof168) (cpOk (replay start168 proof168) cp169) = true := by
  decide +kernel

end Snake9.LocalWindow.C323FwdDistinct
