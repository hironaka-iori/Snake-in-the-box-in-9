import LocalWindowUnsat.Middle325.Data134
import LocalWindowUnsat.Middle325.Data135

/-! Kernel checks of segments 135-135 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok135 : check start135 proof135 = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
