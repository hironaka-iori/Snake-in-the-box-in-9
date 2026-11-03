import LocalWindowUnsat.ShareWindow144.Data566
import LocalWindowUnsat.ShareWindow144.Data567

/-! Kernel checks of segments 2261-2264 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2261 : check start2261 proof2261 = true := by
  decide +kernel

theorem ok2262 : check start2262 proof2262 = true := by
  decide +kernel

theorem ok2263 : check start2263 proof2263 = true := by
  decide +kernel

theorem ok2264 : andB (check start2264 proof2264) (cpOk (replay start2264 proof2264) start2265) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
