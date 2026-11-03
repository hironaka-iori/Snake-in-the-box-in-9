import LocalWindowUnsat.ShareWindow144.Data354
import LocalWindowUnsat.ShareWindow144.Data355

/-! Kernel checks of segments 1413-1416 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1413 : check start1413 proof1413 = true := by
  decide +kernel

theorem ok1414 : check start1414 proof1414 = true := by
  decide +kernel

theorem ok1415 : check start1415 proof1415 = true := by
  decide +kernel

theorem ok1416 : andB (check start1416 proof1416) (cpOk (replay start1416 proof1416) start1417) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
