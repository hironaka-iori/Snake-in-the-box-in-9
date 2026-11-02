import LocalWindowUnsat.Middle325.Data91
import LocalWindowUnsat.Middle325.Data92

/-! Kernel checks of segments 92-92 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok92 : andB (check start92 proof92) (cpOk (replay start92 proof92) start93) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
