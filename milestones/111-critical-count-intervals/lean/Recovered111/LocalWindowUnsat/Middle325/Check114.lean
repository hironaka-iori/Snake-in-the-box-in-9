import Recovered111.LocalWindowUnsat.Middle325.Data113
import Recovered111.LocalWindowUnsat.Middle325.Data114

/-! Kernel checks of segments 114-114 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok114 : andB (check start114 proof114) (cpOk (replay start114 proof114) start115) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
