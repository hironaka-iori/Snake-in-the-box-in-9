import LocalWindowUnsat.ShareWindow144.Data322
import LocalWindowUnsat.ShareWindow144.Data323

/-! Kernel checks of segments 1285-1288 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1285 : check start1285 proof1285 = true := by
  decide +kernel

theorem ok1286 : check start1286 proof1286 = true := by
  decide +kernel

theorem ok1287 : check start1287 proof1287 = true := by
  decide +kernel

theorem ok1288 : andB (check start1288 proof1288) (cpOk (replay start1288 proof1288) start1289) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
