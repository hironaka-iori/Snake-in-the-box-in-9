import LocalWindowUnsat.ShareWindow144.Data324
import LocalWindowUnsat.ShareWindow144.Data325

/-! Kernel checks of segments 1293-1296 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1293 : check start1293 proof1293 = true := by
  decide +kernel

theorem ok1294 : check start1294 proof1294 = true := by
  decide +kernel

theorem ok1295 : check start1295 proof1295 = true := by
  decide +kernel

theorem ok1296 : andB (check start1296 proof1296) (cpOk (replay start1296 proof1296) start1297) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
