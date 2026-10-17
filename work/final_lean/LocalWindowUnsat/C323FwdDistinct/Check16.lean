import LocalWindowUnsat.C323FwdDistinct.Data64

/-! Kernel checks of segments 61-64 of `323_fwd_distinct` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C323FwdDistinct
open Snake9.Lrat

theorem ok61 : check start61 proof61 = true := by
  decide +kernel

theorem ok62 : check start62 proof62 = true := by
  decide +kernel

theorem ok63 : andB (check start63 proof63) (cpOk (replay start63 proof63) cp64) = true := by
  decide +kernel

theorem ok64 : check start64 proof64 = true := by
  decide +kernel

end Snake9.LocalWindow.C323FwdDistinct
