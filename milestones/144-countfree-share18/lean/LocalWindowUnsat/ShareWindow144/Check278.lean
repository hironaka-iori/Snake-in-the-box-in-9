import LocalWindowUnsat.ShareWindow144.Data278
import LocalWindowUnsat.ShareWindow144.Data279

/-! Kernel checks of segments 1109-1112 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1109 : check start1109 proof1109 = true := by
  decide +kernel

theorem ok1110 : check start1110 proof1110 = true := by
  decide +kernel

theorem ok1111 : check start1111 proof1111 = true := by
  decide +kernel

theorem ok1112 : andB (check start1112 proof1112) (cpOk (replay start1112 proof1112) start1113) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
