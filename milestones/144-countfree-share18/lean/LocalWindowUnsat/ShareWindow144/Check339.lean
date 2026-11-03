import LocalWindowUnsat.ShareWindow144.Data339
import LocalWindowUnsat.ShareWindow144.Data340

/-! Kernel checks of segments 1353-1356 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1353 : check start1353 proof1353 = true := by
  decide +kernel

theorem ok1354 : check start1354 proof1354 = true := by
  decide +kernel

theorem ok1355 : check start1355 proof1355 = true := by
  decide +kernel

theorem ok1356 : andB (check start1356 proof1356) (cpOk (replay start1356 proof1356) start1357) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
