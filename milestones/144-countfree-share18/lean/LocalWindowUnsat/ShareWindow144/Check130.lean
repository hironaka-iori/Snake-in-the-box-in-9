import LocalWindowUnsat.ShareWindow144.Data130
import LocalWindowUnsat.ShareWindow144.Data131

/-! Kernel checks of segments 517-520 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok517 : check start517 proof517 = true := by
  decide +kernel

theorem ok518 : check start518 proof518 = true := by
  decide +kernel

theorem ok519 : check start519 proof519 = true := by
  decide +kernel

theorem ok520 : andB (check start520 proof520) (cpOk (replay start520 proof520) start521) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
