import LocalWindowUnsat.Middle325.Data173
import LocalWindowUnsat.Middle325.Data174

/-! Kernel checks of segments 174-174 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok174 : andB (check start174 proof174) (cpOk (replay start174 proof174) start175) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
