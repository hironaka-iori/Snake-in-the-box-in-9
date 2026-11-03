import LocalWindowUnsat.ShareWindow144.Data394
import LocalWindowUnsat.ShareWindow144.Data395

/-! Kernel checks of segments 1573-1576 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1573 : check start1573 proof1573 = true := by
  decide +kernel

theorem ok1574 : check start1574 proof1574 = true := by
  decide +kernel

theorem ok1575 : check start1575 proof1575 = true := by
  decide +kernel

theorem ok1576 : andB (check start1576 proof1576) (cpOk (replay start1576 proof1576) start1577) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
