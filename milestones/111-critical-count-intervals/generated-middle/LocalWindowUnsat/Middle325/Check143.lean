import LocalWindowUnsat.Middle325.Data142
import LocalWindowUnsat.Middle325.Data143

/-! Kernel checks of segments 143-143 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok143 : check start143 proof143 = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
