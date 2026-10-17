import LocalWindowUnsat.C2423RevS01203.Data2

/-! Kernel checks of segments 1-2 of `2423_rev_s01203` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C2423RevS01203
open Snake9.Lrat

theorem ok1 : check start1 proof1 = true := by
  decide +kernel

theorem ok2 : andB (check start2 proof2) (hasEmpty (replay start2 proof2) 512) = true := by
  decide +kernel

end Snake9.LocalWindow.C2423RevS01203
