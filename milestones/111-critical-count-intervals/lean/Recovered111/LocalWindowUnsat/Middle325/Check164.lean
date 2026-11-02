import Recovered111.LocalWindowUnsat.Middle325.Data163
import Recovered111.LocalWindowUnsat.Middle325.Data164

/-! Kernel checks of segments 164-164 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok164 : andB (check start164 proof164) (cpOk (replay start164 proof164) start165) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
