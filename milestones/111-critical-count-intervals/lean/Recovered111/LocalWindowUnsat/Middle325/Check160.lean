import Recovered111.LocalWindowUnsat.Middle325.Data159
import Recovered111.LocalWindowUnsat.Middle325.Data160

/-! Kernel checks of segments 160-160 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok160 : andB (check start160 proof160) (cpOk (replay start160 proof160) start161) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
