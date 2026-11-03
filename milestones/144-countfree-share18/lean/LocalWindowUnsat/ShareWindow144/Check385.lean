import LocalWindowUnsat.ShareWindow144.Data385
import LocalWindowUnsat.ShareWindow144.Data386

/-! Kernel checks of segments 1537-1540 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1537 : check start1537 proof1537 = true := by
  decide +kernel

theorem ok1538 : check start1538 proof1538 = true := by
  decide +kernel

theorem ok1539 : check start1539 proof1539 = true := by
  decide +kernel

theorem ok1540 : andB (check start1540 proof1540) (cpOk (replay start1540 proof1540) start1541) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
