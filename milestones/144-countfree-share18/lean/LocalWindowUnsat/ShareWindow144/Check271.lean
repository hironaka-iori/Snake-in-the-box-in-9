import LocalWindowUnsat.ShareWindow144.Data271
import LocalWindowUnsat.ShareWindow144.Data272

/-! Kernel checks of segments 1081-1084 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1081 : check start1081 proof1081 = true := by
  decide +kernel

theorem ok1082 : check start1082 proof1082 = true := by
  decide +kernel

theorem ok1083 : check start1083 proof1083 = true := by
  decide +kernel

theorem ok1084 : andB (check start1084 proof1084) (cpOk (replay start1084 proof1084) start1085) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
