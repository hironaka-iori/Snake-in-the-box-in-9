import LocalWindowUnsat.ShareWindow144.Data378
import LocalWindowUnsat.ShareWindow144.Data379

/-! Kernel checks of segments 1509-1512 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1509 : check start1509 proof1509 = true := by
  decide +kernel

theorem ok1510 : check start1510 proof1510 = true := by
  decide +kernel

theorem ok1511 : check start1511 proof1511 = true := by
  decide +kernel

theorem ok1512 : andB (check start1512 proof1512) (cpOk (replay start1512 proof1512) start1513) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
