import LocalWindowUnsat.Middle325.Data45
import LocalWindowUnsat.Middle325.Data46

/-! Kernel checks of segments 46-46 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok46 : andB (check start46 proof46) (cpOk (replay start46 proof46) start47) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
