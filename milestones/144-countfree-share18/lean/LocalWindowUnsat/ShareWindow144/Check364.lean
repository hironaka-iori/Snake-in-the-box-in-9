import LocalWindowUnsat.ShareWindow144.Data364
import LocalWindowUnsat.ShareWindow144.Data365

/-! Kernel checks of segments 1453-1456 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1453 : check start1453 proof1453 = true := by
  decide +kernel

theorem ok1454 : check start1454 proof1454 = true := by
  decide +kernel

theorem ok1455 : check start1455 proof1455 = true := by
  decide +kernel

theorem ok1456 : andB (check start1456 proof1456) (cpOk (replay start1456 proof1456) start1457) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
