import LocalWindowUnsat.C323FwdDistinct.Data68

/-! Kernel checks of segments 65-68 of `323_fwd_distinct` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C323FwdDistinct
open Snake9.Lrat

theorem ok65 : check start65 proof65 = true := by
  decide +kernel

theorem ok66 : andB (check start66 proof66) (cpOk (replay start66 proof66) cp67) = true := by
  decide +kernel

theorem ok67 : check start67 proof67 = true := by
  decide +kernel

theorem ok68 : check start68 proof68 = true := by
  decide +kernel

end Snake9.LocalWindow.C323FwdDistinct
