import LocalWindowUnsat.ShareWindow144.Data321
import LocalWindowUnsat.ShareWindow144.Data322

/-! Kernel checks of segments 1281-1284 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1281 : check start1281 proof1281 = true := by
  decide +kernel

theorem ok1282 : check start1282 proof1282 = true := by
  decide +kernel

theorem ok1283 : check start1283 proof1283 = true := by
  decide +kernel

theorem ok1284 : andB (check start1284 proof1284) (cpOk (replay start1284 proof1284) start1285) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
