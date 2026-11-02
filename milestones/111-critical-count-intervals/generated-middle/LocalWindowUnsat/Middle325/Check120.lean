import LocalWindowUnsat.Middle325.Data119
import LocalWindowUnsat.Middle325.Data120

/-! Kernel checks of segments 120-120 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok120 : andB (check start120 proof120) (cpOk (replay start120 proof120) start121) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
