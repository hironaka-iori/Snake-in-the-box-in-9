import LocalWindowUnsat.ShareWindow144.Data597
import LocalWindowUnsat.ShareWindow144.Data598

/-! Kernel checks of segments 2385-2388 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2385 : check start2385 proof2385 = true := by
  decide +kernel

theorem ok2386 : check start2386 proof2386 = true := by
  decide +kernel

theorem ok2387 : check start2387 proof2387 = true := by
  decide +kernel

theorem ok2388 : andB (check start2388 proof2388) (cpOk (replay start2388 proof2388) start2389) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
