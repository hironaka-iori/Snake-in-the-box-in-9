import LocalWindowUnsat.ShareWindow144.Data367
import LocalWindowUnsat.ShareWindow144.Data368

/-! Kernel checks of segments 1465-1468 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1465 : check start1465 proof1465 = true := by
  decide +kernel

theorem ok1466 : check start1466 proof1466 = true := by
  decide +kernel

theorem ok1467 : check start1467 proof1467 = true := by
  decide +kernel

theorem ok1468 : andB (check start1468 proof1468) (cpOk (replay start1468 proof1468) start1469) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
