import LocalWindowUnsat.ShareWindow144.Data311
import LocalWindowUnsat.ShareWindow144.Data312

/-! Kernel checks of segments 1241-1244 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1241 : check start1241 proof1241 = true := by
  decide +kernel

theorem ok1242 : check start1242 proof1242 = true := by
  decide +kernel

theorem ok1243 : check start1243 proof1243 = true := by
  decide +kernel

theorem ok1244 : andB (check start1244 proof1244) (cpOk (replay start1244 proof1244) start1245) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
