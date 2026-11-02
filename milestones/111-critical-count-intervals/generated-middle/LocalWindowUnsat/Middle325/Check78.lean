import LocalWindowUnsat.Middle325.Data77
import LocalWindowUnsat.Middle325.Data78

/-! Kernel checks of segments 78-78 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok78 : andB (check start78 proof78) (cpOk (replay start78 proof78) start79) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
