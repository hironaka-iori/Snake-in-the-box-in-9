import LocalWindowUnsat.ShareWindow144.Data369
import LocalWindowUnsat.ShareWindow144.Data370

/-! Kernel checks of segments 1473-1476 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1473 : check start1473 proof1473 = true := by
  decide +kernel

theorem ok1474 : check start1474 proof1474 = true := by
  decide +kernel

theorem ok1475 : check start1475 proof1475 = true := by
  decide +kernel

theorem ok1476 : andB (check start1476 proof1476) (cpOk (replay start1476 proof1476) start1477) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
