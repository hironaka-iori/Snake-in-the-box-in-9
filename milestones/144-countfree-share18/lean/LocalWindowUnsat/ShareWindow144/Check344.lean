import LocalWindowUnsat.ShareWindow144.Data344
import LocalWindowUnsat.ShareWindow144.Data345

/-! Kernel checks of segments 1373-1376 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1373 : check start1373 proof1373 = true := by
  decide +kernel

theorem ok1374 : check start1374 proof1374 = true := by
  decide +kernel

theorem ok1375 : check start1375 proof1375 = true := by
  decide +kernel

theorem ok1376 : andB (check start1376 proof1376) (cpOk (replay start1376 proof1376) start1377) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
