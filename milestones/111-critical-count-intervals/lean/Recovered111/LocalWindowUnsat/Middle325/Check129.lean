import Recovered111.LocalWindowUnsat.Middle325.Data128
import Recovered111.LocalWindowUnsat.Middle325.Data129

/-! Kernel checks of segments 129-129 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok129 : check start129 proof129 = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
