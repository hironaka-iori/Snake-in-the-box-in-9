import LocalWindowUnsat.ShareWindow144.Data386
import LocalWindowUnsat.ShareWindow144.Data387

/-! Kernel checks of segments 1541-1544 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1541 : check start1541 proof1541 = true := by
  decide +kernel

theorem ok1542 : check start1542 proof1542 = true := by
  decide +kernel

theorem ok1543 : check start1543 proof1543 = true := by
  decide +kernel

theorem ok1544 : andB (check start1544 proof1544) (cpOk (replay start1544 proof1544) start1545) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
