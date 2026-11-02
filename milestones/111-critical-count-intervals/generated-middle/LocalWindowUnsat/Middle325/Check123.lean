import LocalWindowUnsat.Middle325.Data122
import LocalWindowUnsat.Middle325.Data123

/-! Kernel checks of segments 123-123 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok123 : check start123 proof123 = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
