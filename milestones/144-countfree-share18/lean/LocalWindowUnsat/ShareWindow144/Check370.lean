import LocalWindowUnsat.ShareWindow144.Data370
import LocalWindowUnsat.ShareWindow144.Data371

/-! Kernel checks of segments 1477-1480 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1477 : check start1477 proof1477 = true := by
  decide +kernel

theorem ok1478 : check start1478 proof1478 = true := by
  decide +kernel

theorem ok1479 : check start1479 proof1479 = true := by
  decide +kernel

theorem ok1480 : andB (check start1480 proof1480) (cpOk (replay start1480 proof1480) start1481) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
