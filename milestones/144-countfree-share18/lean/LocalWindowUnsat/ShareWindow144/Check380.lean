import LocalWindowUnsat.ShareWindow144.Data380
import LocalWindowUnsat.ShareWindow144.Data381

/-! Kernel checks of segments 1517-1520 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1517 : check start1517 proof1517 = true := by
  decide +kernel

theorem ok1518 : check start1518 proof1518 = true := by
  decide +kernel

theorem ok1519 : check start1519 proof1519 = true := by
  decide +kernel

theorem ok1520 : andB (check start1520 proof1520) (cpOk (replay start1520 proof1520) start1521) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
