import LocalWindowUnsat.ShareWindow144.Data353
import LocalWindowUnsat.ShareWindow144.Data354

/-! Kernel checks of segments 1409-1412 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1409 : check start1409 proof1409 = true := by
  decide +kernel

theorem ok1410 : check start1410 proof1410 = true := by
  decide +kernel

theorem ok1411 : check start1411 proof1411 = true := by
  decide +kernel

theorem ok1412 : andB (check start1412 proof1412) (cpOk (replay start1412 proof1412) start1413) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
