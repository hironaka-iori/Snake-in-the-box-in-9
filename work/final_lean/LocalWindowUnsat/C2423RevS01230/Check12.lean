import LocalWindowUnsat.C2423RevS01230.Data48

/-! Kernel checks of segments 45-48 of `2423_rev_s01230` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C2423RevS01230
open Snake9.Lrat

theorem ok45 : andB (check start45 proof45) (cpOk (replay start45 proof45) cp46) = true := by
  decide +kernel

theorem ok46 : check start46 proof46 = true := by
  decide +kernel

theorem ok47 : check start47 proof47 = true := by
  decide +kernel

theorem ok48 : andB (check start48 proof48) (cpOk (replay start48 proof48) cp49) = true := by
  decide +kernel

end Snake9.LocalWindow.C2423RevS01230
