import LocalWindowUnsat.Middle325.Data55
import LocalWindowUnsat.Middle325.Data56

/-! Kernel checks of segments 56-56 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok56 : andB (check start56 proof56) (cpOk (replay start56 proof56) start57) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
