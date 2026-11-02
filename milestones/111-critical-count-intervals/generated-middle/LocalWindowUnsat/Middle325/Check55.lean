import LocalWindowUnsat.Middle325.Data54
import LocalWindowUnsat.Middle325.Data55

/-! Kernel checks of segments 55-55 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok55 : check start55 proof55 = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
