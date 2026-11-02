import Recovered111.LocalWindowUnsat.Middle325.Data56
import Recovered111.LocalWindowUnsat.Middle325.Data57

/-! Kernel checks of segments 57-57 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok57 : check start57 proof57 = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
