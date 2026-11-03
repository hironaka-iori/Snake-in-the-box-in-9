import LocalWindowUnsat.ShareWindow144.Data527
import LocalWindowUnsat.ShareWindow144.Data528

/-! Kernel checks of segments 2105-2108 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2105 : check start2105 proof2105 = true := by
  decide +kernel

theorem ok2106 : check start2106 proof2106 = true := by
  decide +kernel

theorem ok2107 : check start2107 proof2107 = true := by
  decide +kernel

theorem ok2108 : andB (check start2108 proof2108) (cpOk (replay start2108 proof2108) start2109) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
