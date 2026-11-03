import LocalWindowUnsat.ShareWindow144.Data319
import LocalWindowUnsat.ShareWindow144.Data320

/-! Kernel checks of segments 1273-1276 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1273 : check start1273 proof1273 = true := by
  decide +kernel

theorem ok1274 : check start1274 proof1274 = true := by
  decide +kernel

theorem ok1275 : check start1275 proof1275 = true := by
  decide +kernel

theorem ok1276 : andB (check start1276 proof1276) (cpOk (replay start1276 proof1276) start1277) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
