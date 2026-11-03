import LocalWindowUnsat.ShareWindow144.Data408
import LocalWindowUnsat.ShareWindow144.Data409

/-! Kernel checks of segments 1629-1632 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1629 : check start1629 proof1629 = true := by
  decide +kernel

theorem ok1630 : check start1630 proof1630 = true := by
  decide +kernel

theorem ok1631 : check start1631 proof1631 = true := by
  decide +kernel

theorem ok1632 : andB (check start1632 proof1632) (cpOk (replay start1632 proof1632) start1633) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
