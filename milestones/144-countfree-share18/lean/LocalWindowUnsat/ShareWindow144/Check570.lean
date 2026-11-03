import LocalWindowUnsat.ShareWindow144.Data570
import LocalWindowUnsat.ShareWindow144.Data571

/-! Kernel checks of segments 2277-2280 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2277 : check start2277 proof2277 = true := by
  decide +kernel

theorem ok2278 : check start2278 proof2278 = true := by
  decide +kernel

theorem ok2279 : check start2279 proof2279 = true := by
  decide +kernel

theorem ok2280 : andB (check start2280 proof2280) (cpOk (replay start2280 proof2280) start2281) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
