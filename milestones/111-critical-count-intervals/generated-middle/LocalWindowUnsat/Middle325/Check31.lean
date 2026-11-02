import LocalWindowUnsat.Middle325.Data30
import LocalWindowUnsat.Middle325.Data31

/-! Kernel checks of segments 31-31 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok31 : check start31 proof31 = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
