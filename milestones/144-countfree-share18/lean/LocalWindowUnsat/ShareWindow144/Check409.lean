import LocalWindowUnsat.ShareWindow144.Data409
import LocalWindowUnsat.ShareWindow144.Data410

/-! Kernel checks of segments 1633-1636 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1633 : check start1633 proof1633 = true := by
  decide +kernel

theorem ok1634 : check start1634 proof1634 = true := by
  decide +kernel

theorem ok1635 : check start1635 proof1635 = true := by
  decide +kernel

theorem ok1636 : andB (check start1636 proof1636) (cpOk (replay start1636 proof1636) start1637) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
