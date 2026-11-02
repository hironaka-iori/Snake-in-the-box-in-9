import Recovered111.LocalWindowUnsat.Middle325.Data153
import Recovered111.LocalWindowUnsat.Middle325.Data154

/-! Kernel checks of segments 154-154 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok154 : andB (check start154 proof154) (cpOk (replay start154 proof154) start155) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
