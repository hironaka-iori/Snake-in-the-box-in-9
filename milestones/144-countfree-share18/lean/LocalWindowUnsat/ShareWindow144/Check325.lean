import LocalWindowUnsat.ShareWindow144.Data325
import LocalWindowUnsat.ShareWindow144.Data326

/-! Kernel checks of segments 1297-1300 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1297 : check start1297 proof1297 = true := by
  decide +kernel

theorem ok1298 : check start1298 proof1298 = true := by
  decide +kernel

theorem ok1299 : check start1299 proof1299 = true := by
  decide +kernel

theorem ok1300 : andB (check start1300 proof1300) (cpOk (replay start1300 proof1300) start1301) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
