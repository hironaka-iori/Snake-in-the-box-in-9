import LocalWindowUnsat.ShareWindow144.Data333
import LocalWindowUnsat.ShareWindow144.Data334

/-! Kernel checks of segments 1329-1332 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1329 : check start1329 proof1329 = true := by
  decide +kernel

theorem ok1330 : check start1330 proof1330 = true := by
  decide +kernel

theorem ok1331 : check start1331 proof1331 = true := by
  decide +kernel

theorem ok1332 : andB (check start1332 proof1332) (cpOk (replay start1332 proof1332) start1333) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
