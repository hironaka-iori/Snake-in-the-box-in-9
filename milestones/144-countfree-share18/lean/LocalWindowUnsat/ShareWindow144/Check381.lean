import LocalWindowUnsat.ShareWindow144.Data381
import LocalWindowUnsat.ShareWindow144.Data382

/-! Kernel checks of segments 1521-1524 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1521 : check start1521 proof1521 = true := by
  decide +kernel

theorem ok1522 : check start1522 proof1522 = true := by
  decide +kernel

theorem ok1523 : check start1523 proof1523 = true := by
  decide +kernel

theorem ok1524 : andB (check start1524 proof1524) (cpOk (replay start1524 proof1524) start1525) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
