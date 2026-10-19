import LocalWindowUnsat.C323FwdDistinct.Data120

/-! Kernel checks of segments 117-120 of `323_fwd_distinct` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C323FwdDistinct
open Snake9.Lrat

theorem ok117 : andB (check start117 proof117) (cpOk (replay start117 proof117) cp118) = true := by
  decide +kernel

theorem ok118 : check start118 proof118 = true := by
  decide +kernel

theorem ok119 : check start119 proof119 = true := by
  decide +kernel

theorem ok120 : andB (check start120 proof120) (cpOk (replay start120 proof120) cp121) = true := by
  decide +kernel

end Snake9.LocalWindow.C323FwdDistinct
