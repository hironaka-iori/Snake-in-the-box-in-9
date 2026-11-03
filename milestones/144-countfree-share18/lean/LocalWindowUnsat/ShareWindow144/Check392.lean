import LocalWindowUnsat.ShareWindow144.Data392
import LocalWindowUnsat.ShareWindow144.Data393

/-! Kernel checks of segments 1565-1568 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1565 : check start1565 proof1565 = true := by
  decide +kernel

theorem ok1566 : check start1566 proof1566 = true := by
  decide +kernel

theorem ok1567 : check start1567 proof1567 = true := by
  decide +kernel

theorem ok1568 : andB (check start1568 proof1568) (cpOk (replay start1568 proof1568) start1569) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
