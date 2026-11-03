import LocalWindowUnsat.ShareWindow144.Data592
import LocalWindowUnsat.ShareWindow144.Data593

/-! Kernel checks of segments 2365-2368 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2365 : check start2365 proof2365 = true := by
  decide +kernel

theorem ok2366 : check start2366 proof2366 = true := by
  decide +kernel

theorem ok2367 : check start2367 proof2367 = true := by
  decide +kernel

theorem ok2368 : andB (check start2368 proof2368) (cpOk (replay start2368 proof2368) start2369) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
