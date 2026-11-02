import Recovered111.LocalWindowUnsat.Middle325.Data109
import Recovered111.LocalWindowUnsat.Middle325.Data110

/-! Kernel checks of segments 110-110 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok110 : andB (check start110 proof110) (cpOk (replay start110 proof110) start111) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
