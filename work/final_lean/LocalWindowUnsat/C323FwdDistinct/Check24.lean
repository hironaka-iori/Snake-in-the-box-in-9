import LocalWindowUnsat.C323FwdDistinct.Data96

/-! Kernel checks of segments 93-96 of `323_fwd_distinct` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C323FwdDistinct
open Snake9.Lrat

theorem ok93 : andB (check start93 proof93) (cpOk (replay start93 proof93) cp94) = true := by
  decide +kernel

theorem ok94 : check start94 proof94 = true := by
  decide +kernel

theorem ok95 : check start95 proof95 = true := by
  decide +kernel

theorem ok96 : andB (check start96 proof96) (cpOk (replay start96 proof96) cp97) = true := by
  decide +kernel

end Snake9.LocalWindow.C323FwdDistinct
