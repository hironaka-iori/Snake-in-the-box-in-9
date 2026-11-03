import LocalWindowUnsat.ShareWindow144.Data443
import LocalWindowUnsat.ShareWindow144.Data444

/-! Kernel checks of segments 1769-1772 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1769 : check start1769 proof1769 = true := by
  decide +kernel

theorem ok1770 : check start1770 proof1770 = true := by
  decide +kernel

theorem ok1771 : check start1771 proof1771 = true := by
  decide +kernel

theorem ok1772 : andB (check start1772 proof1772) (cpOk (replay start1772 proof1772) start1773) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
