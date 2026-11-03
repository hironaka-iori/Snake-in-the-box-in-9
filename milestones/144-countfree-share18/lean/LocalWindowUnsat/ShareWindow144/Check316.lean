import LocalWindowUnsat.ShareWindow144.Data316
import LocalWindowUnsat.ShareWindow144.Data317

/-! Kernel checks of segments 1261-1264 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1261 : check start1261 proof1261 = true := by
  decide +kernel

theorem ok1262 : check start1262 proof1262 = true := by
  decide +kernel

theorem ok1263 : check start1263 proof1263 = true := by
  decide +kernel

theorem ok1264 : andB (check start1264 proof1264) (cpOk (replay start1264 proof1264) start1265) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
