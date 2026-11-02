import LocalWindowUnsat.Middle325.Data73
import LocalWindowUnsat.Middle325.Data74

/-! Kernel checks of segments 74-74 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok74 : andB (check start74 proof74) (cpOk (replay start74 proof74) start75) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
