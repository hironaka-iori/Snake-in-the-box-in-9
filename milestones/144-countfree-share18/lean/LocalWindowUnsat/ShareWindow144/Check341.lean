import LocalWindowUnsat.ShareWindow144.Data341
import LocalWindowUnsat.ShareWindow144.Data342

/-! Kernel checks of segments 1361-1364 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1361 : check start1361 proof1361 = true := by
  decide +kernel

theorem ok1362 : check start1362 proof1362 = true := by
  decide +kernel

theorem ok1363 : check start1363 proof1363 = true := by
  decide +kernel

theorem ok1364 : andB (check start1364 proof1364) (cpOk (replay start1364 proof1364) start1365) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
