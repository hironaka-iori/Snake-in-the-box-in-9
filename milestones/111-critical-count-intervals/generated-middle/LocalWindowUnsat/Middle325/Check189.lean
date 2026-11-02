import LocalWindowUnsat.Middle325.Data188
import LocalWindowUnsat.Middle325.Data189

/-! Kernel checks of segments 189-189 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok189 : check start189 proof189 = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
