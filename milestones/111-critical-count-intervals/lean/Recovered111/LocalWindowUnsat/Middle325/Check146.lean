import Recovered111.LocalWindowUnsat.Middle325.Data145
import Recovered111.LocalWindowUnsat.Middle325.Data146

/-! Kernel checks of segments 146-146 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok146 : andB (check start146 proof146) (cpOk (replay start146 proof146) start147) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
