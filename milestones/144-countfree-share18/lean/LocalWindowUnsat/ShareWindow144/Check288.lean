import LocalWindowUnsat.ShareWindow144.Data288
import LocalWindowUnsat.ShareWindow144.Data289

/-! Kernel checks of segments 1149-1152 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1149 : check start1149 proof1149 = true := by
  decide +kernel

theorem ok1150 : check start1150 proof1150 = true := by
  decide +kernel

theorem ok1151 : check start1151 proof1151 = true := by
  decide +kernel

theorem ok1152 : andB (check start1152 proof1152) (cpOk (replay start1152 proof1152) start1153) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
