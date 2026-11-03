import LocalWindowUnsat.ShareWindow144.Data317
import LocalWindowUnsat.ShareWindow144.Data318

/-! Kernel checks of segments 1265-1268 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1265 : check start1265 proof1265 = true := by
  decide +kernel

theorem ok1266 : check start1266 proof1266 = true := by
  decide +kernel

theorem ok1267 : check start1267 proof1267 = true := by
  decide +kernel

theorem ok1268 : andB (check start1268 proof1268) (cpOk (replay start1268 proof1268) start1269) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
