import LocalWindowUnsat.ShareWindow144.Data262
import LocalWindowUnsat.ShareWindow144.Data263

/-! Kernel checks of segments 1045-1048 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1045 : check start1045 proof1045 = true := by
  decide +kernel

theorem ok1046 : check start1046 proof1046 = true := by
  decide +kernel

theorem ok1047 : check start1047 proof1047 = true := by
  decide +kernel

theorem ok1048 : andB (check start1048 proof1048) (cpOk (replay start1048 proof1048) start1049) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
