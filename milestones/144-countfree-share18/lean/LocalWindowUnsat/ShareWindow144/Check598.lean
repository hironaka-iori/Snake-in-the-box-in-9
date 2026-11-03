import LocalWindowUnsat.ShareWindow144.Data598
import LocalWindowUnsat.ShareWindow144.Data599

/-! Kernel checks of segments 2389-2392 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2389 : check start2389 proof2389 = true := by
  decide +kernel

theorem ok2390 : check start2390 proof2390 = true := by
  decide +kernel

theorem ok2391 : check start2391 proof2391 = true := by
  decide +kernel

theorem ok2392 : andB (check start2392 proof2392) (cpOk (replay start2392 proof2392) start2393) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
