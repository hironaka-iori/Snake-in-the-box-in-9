import LocalWindowUnsat.C323FwdDistinct.Data92

/-! Kernel checks of segments 89-92 of `323_fwd_distinct` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C323FwdDistinct
open Snake9.Lrat

theorem ok89 : check start89 proof89 = true := by
  decide +kernel

theorem ok90 : andB (check start90 proof90) (cpOk (replay start90 proof90) cp91) = true := by
  decide +kernel

theorem ok91 : check start91 proof91 = true := by
  decide +kernel

theorem ok92 : check start92 proof92 = true := by
  decide +kernel

end Snake9.LocalWindow.C323FwdDistinct
