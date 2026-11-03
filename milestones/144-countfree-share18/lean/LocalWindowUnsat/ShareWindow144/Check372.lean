import LocalWindowUnsat.ShareWindow144.Data372
import LocalWindowUnsat.ShareWindow144.Data373

/-! Kernel checks of segments 1485-1488 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1485 : check start1485 proof1485 = true := by
  decide +kernel

theorem ok1486 : check start1486 proof1486 = true := by
  decide +kernel

theorem ok1487 : check start1487 proof1487 = true := by
  decide +kernel

theorem ok1488 : andB (check start1488 proof1488) (cpOk (replay start1488 proof1488) start1489) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
