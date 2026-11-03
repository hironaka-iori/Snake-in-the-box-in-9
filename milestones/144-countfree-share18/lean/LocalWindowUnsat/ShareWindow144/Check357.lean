import LocalWindowUnsat.ShareWindow144.Data357
import LocalWindowUnsat.ShareWindow144.Data358

/-! Kernel checks of segments 1425-1428 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1425 : check start1425 proof1425 = true := by
  decide +kernel

theorem ok1426 : check start1426 proof1426 = true := by
  decide +kernel

theorem ok1427 : check start1427 proof1427 = true := by
  decide +kernel

theorem ok1428 : andB (check start1428 proof1428) (cpOk (replay start1428 proof1428) start1429) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
