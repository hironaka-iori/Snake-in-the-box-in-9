import LocalWindowUnsat.ShareWindow144.Data528
import LocalWindowUnsat.ShareWindow144.Data529

/-! Kernel checks of segments 2109-2112 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2109 : check start2109 proof2109 = true := by
  decide +kernel

theorem ok2110 : check start2110 proof2110 = true := by
  decide +kernel

theorem ok2111 : check start2111 proof2111 = true := by
  decide +kernel

theorem ok2112 : andB (check start2112 proof2112) (cpOk (replay start2112 proof2112) start2113) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
