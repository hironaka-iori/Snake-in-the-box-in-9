import LocalWindowUnsat.ShareWindow144.Data136
import LocalWindowUnsat.ShareWindow144.Data137

/-! Kernel checks of segments 541-544 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok541 : check start541 proof541 = true := by
  decide +kernel

theorem ok542 : check start542 proof542 = true := by
  decide +kernel

theorem ok543 : check start543 proof543 = true := by
  decide +kernel

theorem ok544 : andB (check start544 proof544) (cpOk (replay start544 proof544) start545) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
