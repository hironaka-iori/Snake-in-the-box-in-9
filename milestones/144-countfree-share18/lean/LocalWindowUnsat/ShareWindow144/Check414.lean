import LocalWindowUnsat.ShareWindow144.Data414
import LocalWindowUnsat.ShareWindow144.Data415

/-! Kernel checks of segments 1653-1656 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1653 : check start1653 proof1653 = true := by
  decide +kernel

theorem ok1654 : check start1654 proof1654 = true := by
  decide +kernel

theorem ok1655 : check start1655 proof1655 = true := by
  decide +kernel

theorem ok1656 : andB (check start1656 proof1656) (cpOk (replay start1656 proof1656) start1657) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
