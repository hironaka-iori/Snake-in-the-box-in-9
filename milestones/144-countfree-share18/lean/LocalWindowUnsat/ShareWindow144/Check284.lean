import LocalWindowUnsat.ShareWindow144.Data284
import LocalWindowUnsat.ShareWindow144.Data285

/-! Kernel checks of segments 1133-1136 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1133 : check start1133 proof1133 = true := by
  decide +kernel

theorem ok1134 : check start1134 proof1134 = true := by
  decide +kernel

theorem ok1135 : check start1135 proof1135 = true := by
  decide +kernel

theorem ok1136 : andB (check start1136 proof1136) (cpOk (replay start1136 proof1136) start1137) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
