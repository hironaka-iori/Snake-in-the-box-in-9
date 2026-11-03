import LocalWindowUnsat.ShareWindow144.Data348
import LocalWindowUnsat.ShareWindow144.Data349

/-! Kernel checks of segments 1389-1392 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1389 : check start1389 proof1389 = true := by
  decide +kernel

theorem ok1390 : check start1390 proof1390 = true := by
  decide +kernel

theorem ok1391 : check start1391 proof1391 = true := by
  decide +kernel

theorem ok1392 : andB (check start1392 proof1392) (cpOk (replay start1392 proof1392) start1393) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
