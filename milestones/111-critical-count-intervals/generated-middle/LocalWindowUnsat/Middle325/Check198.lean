import LocalWindowUnsat.Middle325.Data197
import LocalWindowUnsat.Middle325.Data198

/-! Kernel checks of segments 198-198 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok198 : andB (check start198 proof198) (cpOk (replay start198 proof198) start199) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
