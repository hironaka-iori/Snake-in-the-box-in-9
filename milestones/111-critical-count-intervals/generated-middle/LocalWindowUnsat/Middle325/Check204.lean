import LocalWindowUnsat.Middle325.Data203
import LocalWindowUnsat.Middle325.Data204

/-! Kernel checks of segments 204-204 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok204 : andB (check start204 proof204) (cpOk (replay start204 proof204) start205) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
