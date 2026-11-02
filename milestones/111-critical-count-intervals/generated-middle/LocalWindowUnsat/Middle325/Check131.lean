import LocalWindowUnsat.Middle325.Data130
import LocalWindowUnsat.Middle325.Data131

/-! Kernel checks of segments 131-131 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok131 : check start131 proof131 = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
