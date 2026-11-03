import LocalWindowUnsat.ShareWindow144.Data362
import LocalWindowUnsat.ShareWindow144.Data363

/-! Kernel checks of segments 1445-1448 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1445 : check start1445 proof1445 = true := by
  decide +kernel

theorem ok1446 : check start1446 proof1446 = true := by
  decide +kernel

theorem ok1447 : check start1447 proof1447 = true := by
  decide +kernel

theorem ok1448 : andB (check start1448 proof1448) (cpOk (replay start1448 proof1448) start1449) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
