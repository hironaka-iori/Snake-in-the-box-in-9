import LocalWindowUnsat.ShareWindow144.Data290
import LocalWindowUnsat.ShareWindow144.Data291

/-! Kernel checks of segments 1157-1160 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1157 : check start1157 proof1157 = true := by
  decide +kernel

theorem ok1158 : check start1158 proof1158 = true := by
  decide +kernel

theorem ok1159 : check start1159 proof1159 = true := by
  decide +kernel

theorem ok1160 : andB (check start1160 proof1160) (cpOk (replay start1160 proof1160) start1161) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
