import LocalWindowUnsat.ShareWindow144.Data382
import LocalWindowUnsat.ShareWindow144.Data383

/-! Kernel checks of segments 1525-1528 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1525 : check start1525 proof1525 = true := by
  decide +kernel

theorem ok1526 : check start1526 proof1526 = true := by
  decide +kernel

theorem ok1527 : check start1527 proof1527 = true := by
  decide +kernel

theorem ok1528 : andB (check start1528 proof1528) (cpOk (replay start1528 proof1528) start1529) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
