import LocalWindowUnsat.ShareWindow144.Data398
import LocalWindowUnsat.ShareWindow144.Data399

/-! Kernel checks of segments 1589-1592 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1589 : check start1589 proof1589 = true := by
  decide +kernel

theorem ok1590 : check start1590 proof1590 = true := by
  decide +kernel

theorem ok1591 : check start1591 proof1591 = true := by
  decide +kernel

theorem ok1592 : andB (check start1592 proof1592) (cpOk (replay start1592 proof1592) start1593) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
