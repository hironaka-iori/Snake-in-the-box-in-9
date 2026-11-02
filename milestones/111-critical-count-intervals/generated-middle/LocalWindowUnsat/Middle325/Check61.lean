import LocalWindowUnsat.Middle325.Data60
import LocalWindowUnsat.Middle325.Data61

/-! Kernel checks of segments 61-61 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok61 : check start61 proof61 = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
