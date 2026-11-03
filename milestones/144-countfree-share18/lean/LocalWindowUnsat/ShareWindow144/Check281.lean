import LocalWindowUnsat.ShareWindow144.Data281
import LocalWindowUnsat.ShareWindow144.Data282

/-! Kernel checks of segments 1121-1124 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1121 : check start1121 proof1121 = true := by
  decide +kernel

theorem ok1122 : check start1122 proof1122 = true := by
  decide +kernel

theorem ok1123 : check start1123 proof1123 = true := by
  decide +kernel

theorem ok1124 : andB (check start1124 proof1124) (cpOk (replay start1124 proof1124) start1125) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
