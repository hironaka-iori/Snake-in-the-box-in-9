import LocalWindowUnsat.ShareWindow144.Data402
import LocalWindowUnsat.ShareWindow144.Data403

/-! Kernel checks of segments 1605-1608 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1605 : check start1605 proof1605 = true := by
  decide +kernel

theorem ok1606 : check start1606 proof1606 = true := by
  decide +kernel

theorem ok1607 : check start1607 proof1607 = true := by
  decide +kernel

theorem ok1608 : andB (check start1608 proof1608) (cpOk (replay start1608 proof1608) start1609) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
