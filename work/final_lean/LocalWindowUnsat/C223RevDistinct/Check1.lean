import LocalWindowUnsat.C223RevDistinct.Data4

/-! Kernel checks of segments 1-4 of `223_rev_distinct` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C223RevDistinct
open Snake9.Lrat

theorem ok1 : check start1 proof1 = true := by
  decide +kernel

theorem ok2 : check start2 proof2 = true := by
  decide +kernel

theorem ok3 : andB (check start3 proof3) (cpOk (replay start3 proof3) cp4) = true := by
  decide +kernel

theorem ok4 : check start4 proof4 = true := by
  decide +kernel

end Snake9.LocalWindow.C223RevDistinct
