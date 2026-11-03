import LocalWindowUnsat.ShareWindow144.Data391
import LocalWindowUnsat.ShareWindow144.Data392

/-! Kernel checks of segments 1561-1564 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1561 : check start1561 proof1561 = true := by
  decide +kernel

theorem ok1562 : check start1562 proof1562 = true := by
  decide +kernel

theorem ok1563 : check start1563 proof1563 = true := by
  decide +kernel

theorem ok1564 : andB (check start1564 proof1564) (cpOk (replay start1564 proof1564) start1565) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
