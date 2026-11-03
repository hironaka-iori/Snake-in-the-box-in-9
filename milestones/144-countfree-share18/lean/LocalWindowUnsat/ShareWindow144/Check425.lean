import LocalWindowUnsat.ShareWindow144.Data425
import LocalWindowUnsat.ShareWindow144.Data426

/-! Kernel checks of segments 1697-1700 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1697 : check start1697 proof1697 = true := by
  decide +kernel

theorem ok1698 : check start1698 proof1698 = true := by
  decide +kernel

theorem ok1699 : check start1699 proof1699 = true := by
  decide +kernel

theorem ok1700 : andB (check start1700 proof1700) (cpOk (replay start1700 proof1700) start1701) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
