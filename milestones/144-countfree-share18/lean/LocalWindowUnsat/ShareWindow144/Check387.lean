import LocalWindowUnsat.ShareWindow144.Data387
import LocalWindowUnsat.ShareWindow144.Data388

/-! Kernel checks of segments 1545-1548 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1545 : check start1545 proof1545 = true := by
  decide +kernel

theorem ok1546 : check start1546 proof1546 = true := by
  decide +kernel

theorem ok1547 : check start1547 proof1547 = true := by
  decide +kernel

theorem ok1548 : andB (check start1548 proof1548) (cpOk (replay start1548 proof1548) start1549) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
