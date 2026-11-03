import LocalWindowUnsat.ShareWindow144.Data332
import LocalWindowUnsat.ShareWindow144.Data333

/-! Kernel checks of segments 1325-1328 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1325 : check start1325 proof1325 = true := by
  decide +kernel

theorem ok1326 : check start1326 proof1326 = true := by
  decide +kernel

theorem ok1327 : check start1327 proof1327 = true := by
  decide +kernel

theorem ok1328 : andB (check start1328 proof1328) (cpOk (replay start1328 proof1328) start1329) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
