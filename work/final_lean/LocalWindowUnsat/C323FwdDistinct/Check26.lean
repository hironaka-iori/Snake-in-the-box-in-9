import LocalWindowUnsat.C323FwdDistinct.Data104

/-! Kernel checks of segments 101-104 of `323_fwd_distinct` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C323FwdDistinct
open Snake9.Lrat

theorem ok101 : check start101 proof101 = true := by
  decide +kernel

theorem ok102 : andB (check start102 proof102) (cpOk (replay start102 proof102) cp103) = true := by
  decide +kernel

theorem ok103 : check start103 proof103 = true := by
  decide +kernel

theorem ok104 : check start104 proof104 = true := by
  decide +kernel

end Snake9.LocalWindow.C323FwdDistinct
