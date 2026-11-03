import LocalWindowUnsat.ShareWindow144.Data371
import LocalWindowUnsat.ShareWindow144.Data372

/-! Kernel checks of segments 1481-1484 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1481 : check start1481 proof1481 = true := by
  decide +kernel

theorem ok1482 : check start1482 proof1482 = true := by
  decide +kernel

theorem ok1483 : check start1483 proof1483 = true := by
  decide +kernel

theorem ok1484 : andB (check start1484 proof1484) (cpOk (replay start1484 proof1484) start1485) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
