import LocalWindowUnsat.ShareWindow144.Data299
import LocalWindowUnsat.ShareWindow144.Data300

/-! Kernel checks of segments 1193-1196 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1193 : check start1193 proof1193 = true := by
  decide +kernel

theorem ok1194 : check start1194 proof1194 = true := by
  decide +kernel

theorem ok1195 : check start1195 proof1195 = true := by
  decide +kernel

theorem ok1196 : andB (check start1196 proof1196) (cpOk (replay start1196 proof1196) start1197) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
