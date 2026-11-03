import LocalWindowUnsat.ShareWindow144.Data289
import LocalWindowUnsat.ShareWindow144.Data290

/-! Kernel checks of segments 1153-1156 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1153 : check start1153 proof1153 = true := by
  decide +kernel

theorem ok1154 : check start1154 proof1154 = true := by
  decide +kernel

theorem ok1155 : check start1155 proof1155 = true := by
  decide +kernel

theorem ok1156 : andB (check start1156 proof1156) (cpOk (replay start1156 proof1156) start1157) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
