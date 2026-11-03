import LocalWindowUnsat.ShareWindow144.Data295
import LocalWindowUnsat.ShareWindow144.Data296

/-! Kernel checks of segments 1177-1180 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1177 : check start1177 proof1177 = true := by
  decide +kernel

theorem ok1178 : check start1178 proof1178 = true := by
  decide +kernel

theorem ok1179 : check start1179 proof1179 = true := by
  decide +kernel

theorem ok1180 : andB (check start1180 proof1180) (cpOk (replay start1180 proof1180) start1181) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
