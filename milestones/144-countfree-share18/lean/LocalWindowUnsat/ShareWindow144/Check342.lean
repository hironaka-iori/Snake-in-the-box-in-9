import LocalWindowUnsat.ShareWindow144.Data342
import LocalWindowUnsat.ShareWindow144.Data343

/-! Kernel checks of segments 1365-1368 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1365 : check start1365 proof1365 = true := by
  decide +kernel

theorem ok1366 : check start1366 proof1366 = true := by
  decide +kernel

theorem ok1367 : check start1367 proof1367 = true := by
  decide +kernel

theorem ok1368 : andB (check start1368 proof1368) (cpOk (replay start1368 proof1368) start1369) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
