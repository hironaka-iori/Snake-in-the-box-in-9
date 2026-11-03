import LocalWindowUnsat.ShareWindow144.Data541
import LocalWindowUnsat.ShareWindow144.Data542

/-! Kernel checks of segments 2161-2164 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2161 : check start2161 proof2161 = true := by
  decide +kernel

theorem ok2162 : check start2162 proof2162 = true := by
  decide +kernel

theorem ok2163 : check start2163 proof2163 = true := by
  decide +kernel

theorem ok2164 : andB (check start2164 proof2164) (cpOk (replay start2164 proof2164) start2165) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
