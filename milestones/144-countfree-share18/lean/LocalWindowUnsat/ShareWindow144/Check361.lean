import LocalWindowUnsat.ShareWindow144.Data361
import LocalWindowUnsat.ShareWindow144.Data362

/-! Kernel checks of segments 1441-1444 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1441 : check start1441 proof1441 = true := by
  decide +kernel

theorem ok1442 : check start1442 proof1442 = true := by
  decide +kernel

theorem ok1443 : check start1443 proof1443 = true := by
  decide +kernel

theorem ok1444 : andB (check start1444 proof1444) (cpOk (replay start1444 proof1444) start1445) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
