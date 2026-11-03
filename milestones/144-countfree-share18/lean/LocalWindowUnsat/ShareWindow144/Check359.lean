import LocalWindowUnsat.ShareWindow144.Data359
import LocalWindowUnsat.ShareWindow144.Data360

/-! Kernel checks of segments 1433-1436 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1433 : check start1433 proof1433 = true := by
  decide +kernel

theorem ok1434 : check start1434 proof1434 = true := by
  decide +kernel

theorem ok1435 : check start1435 proof1435 = true := by
  decide +kernel

theorem ok1436 : andB (check start1436 proof1436) (cpOk (replay start1436 proof1436) start1437) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
