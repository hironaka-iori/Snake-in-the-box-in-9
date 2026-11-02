import LocalWindowUnsat.Middle325.Data143
import LocalWindowUnsat.Middle325.Data144

/-! Kernel checks of segments 144-144 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok144 : andB (check start144 proof144) (cpOk (replay start144 proof144) start145) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
