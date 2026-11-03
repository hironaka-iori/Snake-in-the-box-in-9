import LocalWindowUnsat.ShareWindow144.Data375
import LocalWindowUnsat.ShareWindow144.Data376

/-! Kernel checks of segments 1497-1500 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1497 : check start1497 proof1497 = true := by
  decide +kernel

theorem ok1498 : check start1498 proof1498 = true := by
  decide +kernel

theorem ok1499 : check start1499 proof1499 = true := by
  decide +kernel

theorem ok1500 : andB (check start1500 proof1500) (cpOk (replay start1500 proof1500) start1501) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
