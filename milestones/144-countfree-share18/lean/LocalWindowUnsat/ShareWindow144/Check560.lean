import LocalWindowUnsat.ShareWindow144.Data560
import LocalWindowUnsat.ShareWindow144.Data561

/-! Kernel checks of segments 2237-2240 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2237 : check start2237 proof2237 = true := by
  decide +kernel

theorem ok2238 : check start2238 proof2238 = true := by
  decide +kernel

theorem ok2239 : check start2239 proof2239 = true := by
  decide +kernel

theorem ok2240 : andB (check start2240 proof2240) (cpOk (replay start2240 proof2240) start2241) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
