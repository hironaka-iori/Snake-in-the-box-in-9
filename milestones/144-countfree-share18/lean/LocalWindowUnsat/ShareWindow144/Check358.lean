import LocalWindowUnsat.ShareWindow144.Data358
import LocalWindowUnsat.ShareWindow144.Data359

/-! Kernel checks of segments 1429-1432 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1429 : check start1429 proof1429 = true := by
  decide +kernel

theorem ok1430 : check start1430 proof1430 = true := by
  decide +kernel

theorem ok1431 : check start1431 proof1431 = true := by
  decide +kernel

theorem ok1432 : andB (check start1432 proof1432) (cpOk (replay start1432 proof1432) start1433) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
