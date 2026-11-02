import LocalWindowUnsat.Middle325.Data28
import LocalWindowUnsat.Middle325.Data29

/-! Kernel checks of segments 29-29 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok29 : check start29 proof29 = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
