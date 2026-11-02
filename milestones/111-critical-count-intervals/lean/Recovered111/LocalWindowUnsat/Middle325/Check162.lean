import Recovered111.LocalWindowUnsat.Middle325.Data161
import Recovered111.LocalWindowUnsat.Middle325.Data162

/-! Kernel checks of segments 162-162 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok162 : andB (check start162 proof162) (cpOk (replay start162 proof162) start163) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
