import LocalWindowUnsat.ShareWindow144.Data365
import LocalWindowUnsat.ShareWindow144.Data366

/-! Kernel checks of segments 1457-1460 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1457 : check start1457 proof1457 = true := by
  decide +kernel

theorem ok1458 : check start1458 proof1458 = true := by
  decide +kernel

theorem ok1459 : check start1459 proof1459 = true := by
  decide +kernel

theorem ok1460 : andB (check start1460 proof1460) (cpOk (replay start1460 proof1460) start1461) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
