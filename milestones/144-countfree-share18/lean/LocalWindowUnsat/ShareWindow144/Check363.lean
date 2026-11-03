import LocalWindowUnsat.ShareWindow144.Data363
import LocalWindowUnsat.ShareWindow144.Data364

/-! Kernel checks of segments 1449-1452 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1449 : check start1449 proof1449 = true := by
  decide +kernel

theorem ok1450 : check start1450 proof1450 = true := by
  decide +kernel

theorem ok1451 : check start1451 proof1451 = true := by
  decide +kernel

theorem ok1452 : andB (check start1452 proof1452) (cpOk (replay start1452 proof1452) start1453) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
