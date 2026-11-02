import LocalWindowUnsat.Middle325.Data146
import LocalWindowUnsat.Middle325.Data147

/-! Kernel checks of segments 147-147 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok147 : check start147 proof147 = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
