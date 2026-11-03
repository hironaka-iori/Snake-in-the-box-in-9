import LocalWindowUnsat.ShareWindow144.Data269
import LocalWindowUnsat.ShareWindow144.Data270

/-! Kernel checks of segments 1073-1076 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1073 : check start1073 proof1073 = true := by
  decide +kernel

theorem ok1074 : check start1074 proof1074 = true := by
  decide +kernel

theorem ok1075 : check start1075 proof1075 = true := by
  decide +kernel

theorem ok1076 : andB (check start1076 proof1076) (cpOk (replay start1076 proof1076) start1077) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
