import LocalWindowUnsat.ShareWindow144.Data283
import LocalWindowUnsat.ShareWindow144.Data284

/-! Kernel checks of segments 1129-1132 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1129 : check start1129 proof1129 = true := by
  decide +kernel

theorem ok1130 : check start1130 proof1130 = true := by
  decide +kernel

theorem ok1131 : check start1131 proof1131 = true := by
  decide +kernel

theorem ok1132 : andB (check start1132 proof1132) (cpOk (replay start1132 proof1132) start1133) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
