import LocalWindowUnsat.ShareWindow144.Data352
import LocalWindowUnsat.ShareWindow144.Data353

/-! Kernel checks of segments 1405-1408 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1405 : check start1405 proof1405 = true := by
  decide +kernel

theorem ok1406 : check start1406 proof1406 = true := by
  decide +kernel

theorem ok1407 : check start1407 proof1407 = true := by
  decide +kernel

theorem ok1408 : andB (check start1408 proof1408) (cpOk (replay start1408 proof1408) start1409) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
