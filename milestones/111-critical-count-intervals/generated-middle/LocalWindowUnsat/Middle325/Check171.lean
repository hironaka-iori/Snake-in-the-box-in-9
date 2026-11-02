import LocalWindowUnsat.Middle325.Data170
import LocalWindowUnsat.Middle325.Data171

/-! Kernel checks of segments 171-171 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok171 : check start171 proof171 = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
