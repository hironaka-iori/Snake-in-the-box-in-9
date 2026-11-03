import LocalWindowUnsat.ShareWindow144.Data347
import LocalWindowUnsat.ShareWindow144.Data348

/-! Kernel checks of segments 1385-1388 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1385 : check start1385 proof1385 = true := by
  decide +kernel

theorem ok1386 : check start1386 proof1386 = true := by
  decide +kernel

theorem ok1387 : check start1387 proof1387 = true := by
  decide +kernel

theorem ok1388 : andB (check start1388 proof1388) (cpOk (replay start1388 proof1388) start1389) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
