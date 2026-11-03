import LocalWindowUnsat.ShareWindow144.Data435
import LocalWindowUnsat.ShareWindow144.Data436

/-! Kernel checks of segments 1737-1740 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1737 : check start1737 proof1737 = true := by
  decide +kernel

theorem ok1738 : check start1738 proof1738 = true := by
  decide +kernel

theorem ok1739 : check start1739 proof1739 = true := by
  decide +kernel

theorem ok1740 : andB (check start1740 proof1740) (cpOk (replay start1740 proof1740) start1741) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
