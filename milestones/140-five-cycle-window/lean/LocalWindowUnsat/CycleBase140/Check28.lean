import LocalWindowUnsat.CycleBase140.Data28
import LocalWindowUnsat.CycleBase140.Data29

/-! Kernel checks of segments 109-112 of `base140` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.CycleBase140
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok109 : check start109 proof109 = true := by
  decide +kernel

theorem ok110 : check start110 proof110 = true := by
  decide +kernel

theorem ok111 : check start111 proof111 = true := by
  decide +kernel

theorem ok112 : andB (check start112 proof112) (cpOk (replay start112 proof112) start113) = true := by
  decide +kernel

end Snake9.LocalWindow.CycleBase140
