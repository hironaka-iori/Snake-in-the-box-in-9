import LocalWindowUnsat.ShareWindow144.Data423
import LocalWindowUnsat.ShareWindow144.Data424

/-! Kernel checks of segments 1689-1692 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1689 : check start1689 proof1689 = true := by
  decide +kernel

theorem ok1690 : check start1690 proof1690 = true := by
  decide +kernel

theorem ok1691 : check start1691 proof1691 = true := by
  decide +kernel

theorem ok1692 : andB (check start1692 proof1692) (cpOk (replay start1692 proof1692) start1693) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
