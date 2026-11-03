import LocalWindowUnsat.ShareWindow144.Data379
import LocalWindowUnsat.ShareWindow144.Data380

/-! Kernel checks of segments 1513-1516 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1513 : check start1513 proof1513 = true := by
  decide +kernel

theorem ok1514 : check start1514 proof1514 = true := by
  decide +kernel

theorem ok1515 : check start1515 proof1515 = true := by
  decide +kernel

theorem ok1516 : andB (check start1516 proof1516) (cpOk (replay start1516 proof1516) start1517) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
