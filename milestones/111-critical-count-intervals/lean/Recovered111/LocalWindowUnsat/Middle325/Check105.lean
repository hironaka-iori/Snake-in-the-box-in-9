import Recovered111.LocalWindowUnsat.Middle325.Data104
import Recovered111.LocalWindowUnsat.Middle325.Data105

/-! Kernel checks of segments 105-105 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok105 : check start105 proof105 = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
