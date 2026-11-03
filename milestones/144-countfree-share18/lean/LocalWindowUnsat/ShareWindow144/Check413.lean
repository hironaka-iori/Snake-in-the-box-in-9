import LocalWindowUnsat.ShareWindow144.Data413
import LocalWindowUnsat.ShareWindow144.Data414

/-! Kernel checks of segments 1649-1652 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1649 : check start1649 proof1649 = true := by
  decide +kernel

theorem ok1650 : check start1650 proof1650 = true := by
  decide +kernel

theorem ok1651 : check start1651 proof1651 = true := by
  decide +kernel

theorem ok1652 : andB (check start1652 proof1652) (cpOk (replay start1652 proof1652) start1653) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
