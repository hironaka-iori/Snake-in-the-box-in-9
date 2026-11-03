import LocalWindowUnsat.ShareWindow144.Data349
import LocalWindowUnsat.ShareWindow144.Data350

/-! Kernel checks of segments 1393-1396 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1393 : check start1393 proof1393 = true := by
  decide +kernel

theorem ok1394 : check start1394 proof1394 = true := by
  decide +kernel

theorem ok1395 : check start1395 proof1395 = true := by
  decide +kernel

theorem ok1396 : andB (check start1396 proof1396) (cpOk (replay start1396 proof1396) start1397) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
