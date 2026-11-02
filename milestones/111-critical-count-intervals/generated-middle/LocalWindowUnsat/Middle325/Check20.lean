import LocalWindowUnsat.Middle325.Data19
import LocalWindowUnsat.Middle325.Data20

/-! Kernel checks of segments 20-20 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok20 : andB (check start20 proof20) (cpOk (replay start20 proof20) start21) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
