import LocalWindowUnsat.Middle325.Data177
import LocalWindowUnsat.Middle325.Data178

/-! Kernel checks of segments 178-178 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok178 : andB (check start178 proof178) (cpOk (replay start178 proof178) start179) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
