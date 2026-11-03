import LocalWindowUnsat.ShareWindow144.Data305
import LocalWindowUnsat.ShareWindow144.Data306

/-! Kernel checks of segments 1217-1220 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1217 : check start1217 proof1217 = true := by
  decide +kernel

theorem ok1218 : check start1218 proof1218 = true := by
  decide +kernel

theorem ok1219 : check start1219 proof1219 = true := by
  decide +kernel

theorem ok1220 : andB (check start1220 proof1220) (cpOk (replay start1220 proof1220) start1221) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
