import LocalWindowUnsat.Middle325.Data46
import LocalWindowUnsat.Middle325.Data47

/-! Kernel checks of segments 47-47 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok47 : check start47 proof47 = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
