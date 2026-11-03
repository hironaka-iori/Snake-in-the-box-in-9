import LocalWindowUnsat.ShareWindow144.Data318
import LocalWindowUnsat.ShareWindow144.Data319

/-! Kernel checks of segments 1269-1272 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1269 : check start1269 proof1269 = true := by
  decide +kernel

theorem ok1270 : check start1270 proof1270 = true := by
  decide +kernel

theorem ok1271 : check start1271 proof1271 = true := by
  decide +kernel

theorem ok1272 : andB (check start1272 proof1272) (cpOk (replay start1272 proof1272) start1273) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
