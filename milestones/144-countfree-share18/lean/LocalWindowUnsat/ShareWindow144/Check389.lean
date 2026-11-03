import LocalWindowUnsat.ShareWindow144.Data389
import LocalWindowUnsat.ShareWindow144.Data390

/-! Kernel checks of segments 1553-1556 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1553 : check start1553 proof1553 = true := by
  decide +kernel

theorem ok1554 : check start1554 proof1554 = true := by
  decide +kernel

theorem ok1555 : check start1555 proof1555 = true := by
  decide +kernel

theorem ok1556 : andB (check start1556 proof1556) (cpOk (replay start1556 proof1556) start1557) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
