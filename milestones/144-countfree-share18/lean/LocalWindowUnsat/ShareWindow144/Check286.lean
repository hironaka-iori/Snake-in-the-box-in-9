import LocalWindowUnsat.ShareWindow144.Data286
import LocalWindowUnsat.ShareWindow144.Data287

/-! Kernel checks of segments 1141-1144 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1141 : check start1141 proof1141 = true := by
  decide +kernel

theorem ok1142 : check start1142 proof1142 = true := by
  decide +kernel

theorem ok1143 : check start1143 proof1143 = true := by
  decide +kernel

theorem ok1144 : andB (check start1144 proof1144) (cpOk (replay start1144 proof1144) start1145) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
