import LocalWindowUnsat.ShareWindow144.Data337
import LocalWindowUnsat.ShareWindow144.Data338

/-! Kernel checks of segments 1345-1348 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1345 : check start1345 proof1345 = true := by
  decide +kernel

theorem ok1346 : check start1346 proof1346 = true := by
  decide +kernel

theorem ok1347 : check start1347 proof1347 = true := by
  decide +kernel

theorem ok1348 : andB (check start1348 proof1348) (cpOk (replay start1348 proof1348) start1349) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
