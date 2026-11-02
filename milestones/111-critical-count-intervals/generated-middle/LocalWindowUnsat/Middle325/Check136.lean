import LocalWindowUnsat.Middle325.Data135
import LocalWindowUnsat.Middle325.Data136

/-! Kernel checks of segments 136-136 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok136 : andB (check start136 proof136) (cpOk (replay start136 proof136) start137) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
