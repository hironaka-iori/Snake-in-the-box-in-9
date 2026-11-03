import LocalWindowUnsat.ShareWindow144.Data298
import LocalWindowUnsat.ShareWindow144.Data299

/-! Kernel checks of segments 1189-1192 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1189 : check start1189 proof1189 = true := by
  decide +kernel

theorem ok1190 : check start1190 proof1190 = true := by
  decide +kernel

theorem ok1191 : check start1191 proof1191 = true := by
  decide +kernel

theorem ok1192 : andB (check start1192 proof1192) (cpOk (replay start1192 proof1192) start1193) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
