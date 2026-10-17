import LocalWindowUnsat.C323FwdDistinct.Data84

/-! Kernel checks of segments 81-84 of `323_fwd_distinct` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C323FwdDistinct
open Snake9.Lrat

theorem ok81 : andB (check start81 proof81) (cpOk (replay start81 proof81) cp82) = true := by
  decide +kernel

theorem ok82 : check start82 proof82 = true := by
  decide +kernel

theorem ok83 : check start83 proof83 = true := by
  decide +kernel

theorem ok84 : andB (check start84 proof84) (cpOk (replay start84 proof84) cp85) = true := by
  decide +kernel

end Snake9.LocalWindow.C323FwdDistinct
