import LocalWindowUnsat.ShareWindow144.Data603
import LocalWindowUnsat.ShareWindow144.Data604

/-! Kernel checks of segments 2409-2412 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2409 : check start2409 proof2409 = true := by
  decide +kernel

theorem ok2410 : check start2410 proof2410 = true := by
  decide +kernel

theorem ok2411 : check start2411 proof2411 = true := by
  decide +kernel

theorem ok2412 : andB (check start2412 proof2412) (cpOk (replay start2412 proof2412) start2413) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
