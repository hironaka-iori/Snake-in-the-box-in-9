import LocalWindowUnsat.ShareWindow144.Data590
import LocalWindowUnsat.ShareWindow144.Data591

/-! Kernel checks of segments 2357-2360 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2357 : check start2357 proof2357 = true := by
  decide +kernel

theorem ok2358 : check start2358 proof2358 = true := by
  decide +kernel

theorem ok2359 : check start2359 proof2359 = true := by
  decide +kernel

theorem ok2360 : andB (check start2360 proof2360) (cpOk (replay start2360 proof2360) start2361) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
