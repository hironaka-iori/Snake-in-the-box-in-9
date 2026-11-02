import LocalWindowUnsat.Middle325.Data88
import LocalWindowUnsat.Middle325.Data89

/-! Kernel checks of segments 89-89 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok89 : check start89 proof89 = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
