import LocalWindowUnsat.Middle325.Data94
import LocalWindowUnsat.Middle325.Data95

/-! Kernel checks of segments 95-95 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok95 : check start95 proof95 = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
