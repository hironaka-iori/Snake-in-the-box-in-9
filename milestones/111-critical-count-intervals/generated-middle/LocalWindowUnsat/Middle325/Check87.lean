import LocalWindowUnsat.Middle325.Data86
import LocalWindowUnsat.Middle325.Data87

/-! Kernel checks of segments 87-87 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok87 : check start87 proof87 = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
