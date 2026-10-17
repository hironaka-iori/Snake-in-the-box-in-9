import LocalWindowUnsat.C323FwdDistinct.Data172

/-! Kernel checks of segments 169-172 of `323_fwd_distinct` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C323FwdDistinct
open Snake9.Lrat

theorem ok169 : check start169 proof169 = true := by
  decide +kernel

theorem ok170 : check start170 proof170 = true := by
  decide +kernel

theorem ok171 : andB (check start171 proof171) (cpOk (replay start171 proof171) cp172) = true := by
  decide +kernel

theorem ok172 : check start172 proof172 = true := by
  decide +kernel

end Snake9.LocalWindow.C323FwdDistinct
