import LocalWindowUnsat.ShareWindow144.Data338
import LocalWindowUnsat.ShareWindow144.Data339

/-! Kernel checks of segments 1349-1352 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1349 : check start1349 proof1349 = true := by
  decide +kernel

theorem ok1350 : check start1350 proof1350 = true := by
  decide +kernel

theorem ok1351 : check start1351 proof1351 = true := by
  decide +kernel

theorem ok1352 : andB (check start1352 proof1352) (cpOk (replay start1352 proof1352) start1353) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
