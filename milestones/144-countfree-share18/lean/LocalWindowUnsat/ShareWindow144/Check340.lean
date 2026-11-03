import LocalWindowUnsat.ShareWindow144.Data340
import LocalWindowUnsat.ShareWindow144.Data341

/-! Kernel checks of segments 1357-1360 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1357 : check start1357 proof1357 = true := by
  decide +kernel

theorem ok1358 : check start1358 proof1358 = true := by
  decide +kernel

theorem ok1359 : check start1359 proof1359 = true := by
  decide +kernel

theorem ok1360 : andB (check start1360 proof1360) (cpOk (replay start1360 proof1360) start1361) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
