import LocalWindowUnsat.C323FwdDistinct.Data140

/-! Kernel checks of segments 137-140 of `323_fwd_distinct` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C323FwdDistinct
open Snake9.Lrat

theorem ok137 : check start137 proof137 = true := by
  decide +kernel

theorem ok138 : andB (check start138 proof138) (cpOk (replay start138 proof138) cp139) = true := by
  decide +kernel

theorem ok139 : check start139 proof139 = true := by
  decide +kernel

theorem ok140 : check start140 proof140 = true := by
  decide +kernel

end Snake9.LocalWindow.C323FwdDistinct
