import LocalWindowUnsat.ShareWindow144.Data373
import LocalWindowUnsat.ShareWindow144.Data374

/-! Kernel checks of segments 1489-1492 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1489 : check start1489 proof1489 = true := by
  decide +kernel

theorem ok1490 : check start1490 proof1490 = true := by
  decide +kernel

theorem ok1491 : check start1491 proof1491 = true := by
  decide +kernel

theorem ok1492 : andB (check start1492 proof1492) (cpOk (replay start1492 proof1492) start1493) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
