import LocalWindowUnsat.Middle325.Data107
import LocalWindowUnsat.Middle325.Data108

/-! Kernel checks of segments 108-108 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok108 : andB (check start108 proof108) (cpOk (replay start108 proof108) start109) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
