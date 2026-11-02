import Recovered111.LocalWindowUnsat.Middle325.Data50
import Recovered111.LocalWindowUnsat.Middle325.Data51

/-! Kernel checks of segments 51-51 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok51 : check start51 proof51 = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
