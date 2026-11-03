import LocalWindowUnsat.ShareWindow144.Data366
import LocalWindowUnsat.ShareWindow144.Data367

/-! Kernel checks of segments 1461-1464 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1461 : check start1461 proof1461 = true := by
  decide +kernel

theorem ok1462 : check start1462 proof1462 = true := by
  decide +kernel

theorem ok1463 : check start1463 proof1463 = true := by
  decide +kernel

theorem ok1464 : andB (check start1464 proof1464) (cpOk (replay start1464 proof1464) start1465) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
