import LocalWindowUnsat.ShareWindow144.Data346
import LocalWindowUnsat.ShareWindow144.Data347

/-! Kernel checks of segments 1381-1384 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1381 : check start1381 proof1381 = true := by
  decide +kernel

theorem ok1382 : check start1382 proof1382 = true := by
  decide +kernel

theorem ok1383 : check start1383 proof1383 = true := by
  decide +kernel

theorem ok1384 : andB (check start1384 proof1384) (cpOk (replay start1384 proof1384) start1385) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
