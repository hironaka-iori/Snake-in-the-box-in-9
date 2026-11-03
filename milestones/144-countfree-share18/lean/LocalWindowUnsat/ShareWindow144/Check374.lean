import LocalWindowUnsat.ShareWindow144.Data374
import LocalWindowUnsat.ShareWindow144.Data375

/-! Kernel checks of segments 1493-1496 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1493 : check start1493 proof1493 = true := by
  decide +kernel

theorem ok1494 : check start1494 proof1494 = true := by
  decide +kernel

theorem ok1495 : check start1495 proof1495 = true := by
  decide +kernel

theorem ok1496 : andB (check start1496 proof1496) (cpOk (replay start1496 proof1496) start1497) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
