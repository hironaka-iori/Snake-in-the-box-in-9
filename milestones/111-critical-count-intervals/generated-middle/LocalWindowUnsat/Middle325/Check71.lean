import LocalWindowUnsat.Middle325.Data70
import LocalWindowUnsat.Middle325.Data71

/-! Kernel checks of segments 71-71 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok71 : check start71 proof71 = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
