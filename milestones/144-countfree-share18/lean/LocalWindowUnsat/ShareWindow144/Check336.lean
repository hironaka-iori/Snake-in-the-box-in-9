import LocalWindowUnsat.ShareWindow144.Data336
import LocalWindowUnsat.ShareWindow144.Data337

/-! Kernel checks of segments 1341-1344 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1341 : check start1341 proof1341 = true := by
  decide +kernel

theorem ok1342 : check start1342 proof1342 = true := by
  decide +kernel

theorem ok1343 : check start1343 proof1343 = true := by
  decide +kernel

theorem ok1344 : andB (check start1344 proof1344) (cpOk (replay start1344 proof1344) start1345) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
