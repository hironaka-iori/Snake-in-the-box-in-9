import LocalWindowUnsat.C323FwdDistinct.Data80

/-! Kernel checks of segments 77-80 of `323_fwd_distinct` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C323FwdDistinct
open Snake9.Lrat

theorem ok77 : check start77 proof77 = true := by
  decide +kernel

theorem ok78 : andB (check start78 proof78) (cpOk (replay start78 proof78) cp79) = true := by
  decide +kernel

theorem ok79 : check start79 proof79 = true := by
  decide +kernel

theorem ok80 : check start80 proof80 = true := by
  decide +kernel

end Snake9.LocalWindow.C323FwdDistinct
