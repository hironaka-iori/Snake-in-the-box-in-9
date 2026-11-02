import Recovered111.LocalWindowUnsat.Middle325.Data13
import Recovered111.LocalWindowUnsat.Middle325.Data14

/-! Kernel checks of segments 14-14 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok14 : andB (check start14 proof14) (cpOk (replay start14 proof14) start15) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
