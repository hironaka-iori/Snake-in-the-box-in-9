import LocalWindowUnsat.ShareWindow144.Data388
import LocalWindowUnsat.ShareWindow144.Data389

/-! Kernel checks of segments 1549-1552 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1549 : check start1549 proof1549 = true := by
  decide +kernel

theorem ok1550 : check start1550 proof1550 = true := by
  decide +kernel

theorem ok1551 : check start1551 proof1551 = true := by
  decide +kernel

theorem ok1552 : andB (check start1552 proof1552) (cpOk (replay start1552 proof1552) start1553) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
