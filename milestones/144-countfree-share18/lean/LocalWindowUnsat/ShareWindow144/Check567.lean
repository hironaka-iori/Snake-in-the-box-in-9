import LocalWindowUnsat.ShareWindow144.Data567
import LocalWindowUnsat.ShareWindow144.Data568

/-! Kernel checks of segments 2265-2268 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2265 : check start2265 proof2265 = true := by
  decide +kernel

theorem ok2266 : check start2266 proof2266 = true := by
  decide +kernel

theorem ok2267 : check start2267 proof2267 = true := by
  decide +kernel

theorem ok2268 : andB (check start2268 proof2268) (cpOk (replay start2268 proof2268) start2269) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
