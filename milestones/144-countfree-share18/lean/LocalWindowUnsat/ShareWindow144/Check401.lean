import LocalWindowUnsat.ShareWindow144.Data401
import LocalWindowUnsat.ShareWindow144.Data402

/-! Kernel checks of segments 1601-1604 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1601 : check start1601 proof1601 = true := by
  decide +kernel

theorem ok1602 : check start1602 proof1602 = true := by
  decide +kernel

theorem ok1603 : check start1603 proof1603 = true := by
  decide +kernel

theorem ok1604 : andB (check start1604 proof1604) (cpOk (replay start1604 proof1604) start1605) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
