import LocalWindowUnsat.C2423RevS01230.Data24

/-! Kernel checks of segments 21-24 of `2423_rev_s01230` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C2423RevS01230
open Snake9.Lrat

theorem ok21 : andB (check start21 proof21) (cpOk (replay start21 proof21) cp22) = true := by
  decide +kernel

theorem ok22 : check start22 proof22 = true := by
  decide +kernel

theorem ok23 : check start23 proof23 = true := by
  decide +kernel

theorem ok24 : andB (check start24 proof24) (cpOk (replay start24 proof24) cp25) = true := by
  decide +kernel

end Snake9.LocalWindow.C2423RevS01230
