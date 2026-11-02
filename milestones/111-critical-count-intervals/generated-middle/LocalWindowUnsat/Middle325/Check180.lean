import LocalWindowUnsat.Middle325.Data179
import LocalWindowUnsat.Middle325.Data180

/-! Kernel checks of segments 180-180 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok180 : andB (check start180 proof180) (cpOk (replay start180 proof180) start181) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
