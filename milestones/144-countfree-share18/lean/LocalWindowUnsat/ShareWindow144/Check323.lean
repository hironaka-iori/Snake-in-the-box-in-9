import LocalWindowUnsat.ShareWindow144.Data323
import LocalWindowUnsat.ShareWindow144.Data324

/-! Kernel checks of segments 1289-1292 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1289 : check start1289 proof1289 = true := by
  decide +kernel

theorem ok1290 : check start1290 proof1290 = true := by
  decide +kernel

theorem ok1291 : check start1291 proof1291 = true := by
  decide +kernel

theorem ok1292 : andB (check start1292 proof1292) (cpOk (replay start1292 proof1292) start1293) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
