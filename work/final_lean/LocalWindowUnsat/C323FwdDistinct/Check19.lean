import LocalWindowUnsat.C323FwdDistinct.Data76

/-! Kernel checks of segments 73-76 of `323_fwd_distinct` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C323FwdDistinct
open Snake9.Lrat

theorem ok73 : check start73 proof73 = true := by
  decide +kernel

theorem ok74 : check start74 proof74 = true := by
  decide +kernel

theorem ok75 : andB (check start75 proof75) (cpOk (replay start75 proof75) cp76) = true := by
  decide +kernel

theorem ok76 : check start76 proof76 = true := by
  decide +kernel

end Snake9.LocalWindow.C323FwdDistinct
