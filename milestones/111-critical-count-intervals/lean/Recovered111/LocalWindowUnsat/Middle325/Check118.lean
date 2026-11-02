import Recovered111.LocalWindowUnsat.Middle325.Data117
import Recovered111.LocalWindowUnsat.Middle325.Data118

/-! Kernel checks of segments 118-118 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok118 : andB (check start118 proof118) (cpOk (replay start118 proof118) start119) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
