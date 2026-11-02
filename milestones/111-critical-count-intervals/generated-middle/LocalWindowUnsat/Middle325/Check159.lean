import LocalWindowUnsat.Middle325.Data158
import LocalWindowUnsat.Middle325.Data159

/-! Kernel checks of segments 159-159 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok159 : check start159 proof159 = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
