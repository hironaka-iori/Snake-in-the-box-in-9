import LocalWindowUnsat.Middle325R.Data1
import LocalWindowUnsat.Middle325R.Data2

/-! Kernel checks of segments 1-4 of `middle325r` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325R
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok1 : check start1 proof1 = true := by
  decide +kernel

theorem ok2 : check start2 proof2 = true := by
  decide +kernel

theorem ok3 : check start3 proof3 = true := by
  decide +kernel

theorem ok4 : andB (check start4 proof4) (cpOk (replay start4 proof4) start5) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325R
