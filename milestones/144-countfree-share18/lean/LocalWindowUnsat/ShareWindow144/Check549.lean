import LocalWindowUnsat.ShareWindow144.Data549
import LocalWindowUnsat.ShareWindow144.Data550

/-! Kernel checks of segments 2193-2196 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2193 : check start2193 proof2193 = true := by
  decide +kernel

theorem ok2194 : check start2194 proof2194 = true := by
  decide +kernel

theorem ok2195 : check start2195 proof2195 = true := by
  decide +kernel

theorem ok2196 : andB (check start2196 proof2196) (cpOk (replay start2196 proof2196) start2197) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
