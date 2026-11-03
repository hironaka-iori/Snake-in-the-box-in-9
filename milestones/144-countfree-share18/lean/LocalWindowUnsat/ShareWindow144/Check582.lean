import LocalWindowUnsat.ShareWindow144.Data582
import LocalWindowUnsat.ShareWindow144.Data583

/-! Kernel checks of segments 2325-2328 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2325 : check start2325 proof2325 = true := by
  decide +kernel

theorem ok2326 : check start2326 proof2326 = true := by
  decide +kernel

theorem ok2327 : check start2327 proof2327 = true := by
  decide +kernel

theorem ok2328 : andB (check start2328 proof2328) (cpOk (replay start2328 proof2328) start2329) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
