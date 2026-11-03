import LocalWindowUnsat.ShareWindow144.Data251
import LocalWindowUnsat.ShareWindow144.Data252

/-! Kernel checks of segments 1001-1004 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1001 : check start1001 proof1001 = true := by
  decide +kernel

theorem ok1002 : check start1002 proof1002 = true := by
  decide +kernel

theorem ok1003 : check start1003 proof1003 = true := by
  decide +kernel

theorem ok1004 : andB (check start1004 proof1004) (cpOk (replay start1004 proof1004) start1005) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
