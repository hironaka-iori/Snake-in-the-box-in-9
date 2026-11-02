import Recovered111.LocalWindowUnsat.Middle325.Data76
import Recovered111.LocalWindowUnsat.Middle325.Data77

/-! Kernel checks of segments 77-77 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok77 : check start77 proof77 = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
