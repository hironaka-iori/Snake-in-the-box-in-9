import Recovered111.LocalWindowUnsat.Middle325.Data99
import Recovered111.LocalWindowUnsat.Middle325.Data100

/-! Kernel checks of segments 100-100 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok100 : andB (check start100 proof100) (cpOk (replay start100 proof100) start101) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
