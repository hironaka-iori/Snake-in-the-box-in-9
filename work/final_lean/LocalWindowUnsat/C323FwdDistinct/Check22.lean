import LocalWindowUnsat.C323FwdDistinct.Data88

/-! Kernel checks of segments 85-88 of `323_fwd_distinct` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C323FwdDistinct
open Snake9.Lrat

theorem ok85 : check start85 proof85 = true := by
  decide +kernel

theorem ok86 : check start86 proof86 = true := by
  decide +kernel

theorem ok87 : andB (check start87 proof87) (cpOk (replay start87 proof87) cp88) = true := by
  decide +kernel

theorem ok88 : check start88 proof88 = true := by
  decide +kernel

end Snake9.LocalWindow.C323FwdDistinct
