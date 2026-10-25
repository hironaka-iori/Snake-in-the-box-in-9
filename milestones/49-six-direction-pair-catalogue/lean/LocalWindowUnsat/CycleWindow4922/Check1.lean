import LocalWindowUnsat.CycleWindow4922.Data0
import LocalWindowUnsat.CycleWindow4922.Data1
import LocalWindowUnsat.CycleWindow4922.Data2

/-! Kernel checks of segments 1-2 of `cycle4922` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.CycleWindow4922
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok1 : check start1 proof1 = true := by
  decide +kernel

theorem ok2 : andB (check start2 proof2) (hasEmpty (replay start2 proof2) 512) = true := by
  decide +kernel

end Snake9.LocalWindow.CycleWindow4922
