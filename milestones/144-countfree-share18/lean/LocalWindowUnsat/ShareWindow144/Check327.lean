import LocalWindowUnsat.ShareWindow144.Data327
import LocalWindowUnsat.ShareWindow144.Data328

/-! Kernel checks of segments 1305-1308 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1305 : check start1305 proof1305 = true := by
  decide +kernel

theorem ok1306 : check start1306 proof1306 = true := by
  decide +kernel

theorem ok1307 : check start1307 proof1307 = true := by
  decide +kernel

theorem ok1308 : andB (check start1308 proof1308) (cpOk (replay start1308 proof1308) start1309) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
