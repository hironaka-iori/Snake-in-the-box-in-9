import LocalWindowUnsat.C323FwdDistinct.Data108

/-! Kernel checks of segments 105-108 of `323_fwd_distinct` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C323FwdDistinct
open Snake9.Lrat

theorem ok105 : andB (check start105 proof105) (cpOk (replay start105 proof105) cp106) = true := by
  decide +kernel

theorem ok106 : check start106 proof106 = true := by
  decide +kernel

theorem ok107 : check start107 proof107 = true := by
  decide +kernel

theorem ok108 : andB (check start108 proof108) (cpOk (replay start108 proof108) cp109) = true := by
  decide +kernel

end Snake9.LocalWindow.C323FwdDistinct
