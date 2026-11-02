import LocalWindowUnsat.Middle325.Data137
import LocalWindowUnsat.Middle325.Data138

/-! Kernel checks of segments 138-138 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok138 : andB (check start138 proof138) (cpOk (replay start138 proof138) start139) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
