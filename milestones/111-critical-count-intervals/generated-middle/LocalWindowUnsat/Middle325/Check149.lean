import LocalWindowUnsat.Middle325.Data148
import LocalWindowUnsat.Middle325.Data149

/-! Kernel checks of segments 149-149 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok149 : check start149 proof149 = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
