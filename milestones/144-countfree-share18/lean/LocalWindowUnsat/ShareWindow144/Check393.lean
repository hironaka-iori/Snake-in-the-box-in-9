import LocalWindowUnsat.ShareWindow144.Data393
import LocalWindowUnsat.ShareWindow144.Data394

/-! Kernel checks of segments 1569-1572 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1569 : check start1569 proof1569 = true := by
  decide +kernel

theorem ok1570 : check start1570 proof1570 = true := by
  decide +kernel

theorem ok1571 : check start1571 proof1571 = true := by
  decide +kernel

theorem ok1572 : andB (check start1572 proof1572) (cpOk (replay start1572 proof1572) start1573) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
