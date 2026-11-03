import LocalWindowUnsat.ShareWindow144.Data193
import LocalWindowUnsat.ShareWindow144.Data194

/-! Kernel checks of segments 769-772 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok769 : check start769 proof769 = true := by
  decide +kernel

theorem ok770 : check start770 proof770 = true := by
  decide +kernel

theorem ok771 : check start771 proof771 = true := by
  decide +kernel

theorem ok772 : andB (check start772 proof772) (cpOk (replay start772 proof772) start773) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
