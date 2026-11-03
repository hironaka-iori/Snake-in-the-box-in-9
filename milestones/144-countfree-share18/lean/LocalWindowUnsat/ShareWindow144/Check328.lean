import LocalWindowUnsat.ShareWindow144.Data328
import LocalWindowUnsat.ShareWindow144.Data329

/-! Kernel checks of segments 1309-1312 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1309 : check start1309 proof1309 = true := by
  decide +kernel

theorem ok1310 : check start1310 proof1310 = true := by
  decide +kernel

theorem ok1311 : check start1311 proof1311 = true := by
  decide +kernel

theorem ok1312 : andB (check start1312 proof1312) (cpOk (replay start1312 proof1312) start1313) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
