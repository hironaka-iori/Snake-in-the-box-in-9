import LocalWindowUnsat.ShareWindow144.Data436
import LocalWindowUnsat.ShareWindow144.Data437

/-! Kernel checks of segments 1741-1744 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1741 : check start1741 proof1741 = true := by
  decide +kernel

theorem ok1742 : check start1742 proof1742 = true := by
  decide +kernel

theorem ok1743 : check start1743 proof1743 = true := by
  decide +kernel

theorem ok1744 : andB (check start1744 proof1744) (cpOk (replay start1744 proof1744) start1745) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
