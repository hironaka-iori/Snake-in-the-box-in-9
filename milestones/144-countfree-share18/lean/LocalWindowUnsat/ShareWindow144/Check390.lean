import LocalWindowUnsat.ShareWindow144.Data390
import LocalWindowUnsat.ShareWindow144.Data391

/-! Kernel checks of segments 1557-1560 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1557 : check start1557 proof1557 = true := by
  decide +kernel

theorem ok1558 : check start1558 proof1558 = true := by
  decide +kernel

theorem ok1559 : check start1559 proof1559 = true := by
  decide +kernel

theorem ok1560 : andB (check start1560 proof1560) (cpOk (replay start1560 proof1560) start1561) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
