import Recovered111.LocalWindowUnsat.Middle325.Data121
import Recovered111.LocalWindowUnsat.Middle325.Data122

/-! Kernel checks of segments 122-122 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok122 : andB (check start122 proof122) (cpOk (replay start122 proof122) start123) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
