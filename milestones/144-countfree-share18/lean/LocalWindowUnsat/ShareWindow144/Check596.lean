import LocalWindowUnsat.ShareWindow144.Data596
import LocalWindowUnsat.ShareWindow144.Data597

/-! Kernel checks of segments 2381-2384 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2381 : check start2381 proof2381 = true := by
  decide +kernel

theorem ok2382 : check start2382 proof2382 = true := by
  decide +kernel

theorem ok2383 : check start2383 proof2383 = true := by
  decide +kernel

theorem ok2384 : andB (check start2384 proof2384) (cpOk (replay start2384 proof2384) start2385) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
