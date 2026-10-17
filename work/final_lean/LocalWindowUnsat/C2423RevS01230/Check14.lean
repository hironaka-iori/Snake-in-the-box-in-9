import LocalWindowUnsat.C2423RevS01230.Data53

/-! Kernel checks of segments 53-53 of `2423_rev_s01230` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C2423RevS01230
open Snake9.Lrat

theorem ok53 : andB (check start53 proof53) (hasEmpty (replay start53 proof53) 1745) = true := by
  decide +kernel

end Snake9.LocalWindow.C2423RevS01230
