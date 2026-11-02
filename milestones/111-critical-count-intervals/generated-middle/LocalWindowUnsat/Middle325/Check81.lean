import LocalWindowUnsat.Middle325.Data80
import LocalWindowUnsat.Middle325.Data81

/-! Kernel checks of segments 81-81 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok81 : check start81 proof81 = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
