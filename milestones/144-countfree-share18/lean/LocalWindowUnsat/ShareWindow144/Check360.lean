import LocalWindowUnsat.ShareWindow144.Data360
import LocalWindowUnsat.ShareWindow144.Data361

/-! Kernel checks of segments 1437-1440 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1437 : check start1437 proof1437 = true := by
  decide +kernel

theorem ok1438 : check start1438 proof1438 = true := by
  decide +kernel

theorem ok1439 : check start1439 proof1439 = true := by
  decide +kernel

theorem ok1440 : andB (check start1440 proof1440) (cpOk (replay start1440 proof1440) start1441) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
