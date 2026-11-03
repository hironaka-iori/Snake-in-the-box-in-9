import LocalWindowUnsat.ShareWindow144.Data399
import LocalWindowUnsat.ShareWindow144.Data400

/-! Kernel checks of segments 1593-1596 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1593 : check start1593 proof1593 = true := by
  decide +kernel

theorem ok1594 : check start1594 proof1594 = true := by
  decide +kernel

theorem ok1595 : check start1595 proof1595 = true := by
  decide +kernel

theorem ok1596 : andB (check start1596 proof1596) (cpOk (replay start1596 proof1596) start1597) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
