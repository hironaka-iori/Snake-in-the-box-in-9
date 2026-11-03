import LocalWindowUnsat.ShareWindow144.Data345
import LocalWindowUnsat.ShareWindow144.Data346

/-! Kernel checks of segments 1377-1380 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1377 : check start1377 proof1377 = true := by
  decide +kernel

theorem ok1378 : check start1378 proof1378 = true := by
  decide +kernel

theorem ok1379 : check start1379 proof1379 = true := by
  decide +kernel

theorem ok1380 : andB (check start1380 proof1380) (cpOk (replay start1380 proof1380) start1381) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
