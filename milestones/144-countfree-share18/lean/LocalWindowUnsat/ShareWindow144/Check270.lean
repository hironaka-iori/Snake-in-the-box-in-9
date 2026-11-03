import LocalWindowUnsat.ShareWindow144.Data270
import LocalWindowUnsat.ShareWindow144.Data271

/-! Kernel checks of segments 1077-1080 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1077 : check start1077 proof1077 = true := by
  decide +kernel

theorem ok1078 : check start1078 proof1078 = true := by
  decide +kernel

theorem ok1079 : check start1079 proof1079 = true := by
  decide +kernel

theorem ok1080 : andB (check start1080 proof1080) (cpOk (replay start1080 proof1080) start1081) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
