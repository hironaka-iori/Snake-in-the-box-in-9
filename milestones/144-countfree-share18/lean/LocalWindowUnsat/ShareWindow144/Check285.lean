import LocalWindowUnsat.ShareWindow144.Data285
import LocalWindowUnsat.ShareWindow144.Data286

/-! Kernel checks of segments 1137-1140 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1137 : check start1137 proof1137 = true := by
  decide +kernel

theorem ok1138 : check start1138 proof1138 = true := by
  decide +kernel

theorem ok1139 : check start1139 proof1139 = true := by
  decide +kernel

theorem ok1140 : andB (check start1140 proof1140) (cpOk (replay start1140 proof1140) start1141) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
