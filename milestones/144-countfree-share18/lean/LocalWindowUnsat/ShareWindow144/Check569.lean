import LocalWindowUnsat.ShareWindow144.Data569
import LocalWindowUnsat.ShareWindow144.Data570

/-! Kernel checks of segments 2273-2276 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2273 : check start2273 proof2273 = true := by
  decide +kernel

theorem ok2274 : check start2274 proof2274 = true := by
  decide +kernel

theorem ok2275 : check start2275 proof2275 = true := by
  decide +kernel

theorem ok2276 : andB (check start2276 proof2276) (cpOk (replay start2276 proof2276) start2277) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
