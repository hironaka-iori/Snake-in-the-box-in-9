import LocalWindowUnsat.ShareWindow144.Data302
import LocalWindowUnsat.ShareWindow144.Data303

/-! Kernel checks of segments 1205-1208 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1205 : check start1205 proof1205 = true := by
  decide +kernel

theorem ok1206 : check start1206 proof1206 = true := by
  decide +kernel

theorem ok1207 : check start1207 proof1207 = true := by
  decide +kernel

theorem ok1208 : andB (check start1208 proof1208) (cpOk (replay start1208 proof1208) start1209) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
