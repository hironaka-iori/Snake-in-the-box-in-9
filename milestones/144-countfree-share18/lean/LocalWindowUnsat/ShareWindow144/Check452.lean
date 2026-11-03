import LocalWindowUnsat.ShareWindow144.Data452
import LocalWindowUnsat.ShareWindow144.Data453

/-! Kernel checks of segments 1805-1808 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1805 : check start1805 proof1805 = true := by
  decide +kernel

theorem ok1806 : check start1806 proof1806 = true := by
  decide +kernel

theorem ok1807 : check start1807 proof1807 = true := by
  decide +kernel

theorem ok1808 : andB (check start1808 proof1808) (cpOk (replay start1808 proof1808) start1809) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
