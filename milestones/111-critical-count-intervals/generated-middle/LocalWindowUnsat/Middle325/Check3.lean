import LocalWindowUnsat.Middle325.Data2
import LocalWindowUnsat.Middle325.Data3

/-! Kernel checks of segments 3-3 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok3 : check start3 proof3 = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
