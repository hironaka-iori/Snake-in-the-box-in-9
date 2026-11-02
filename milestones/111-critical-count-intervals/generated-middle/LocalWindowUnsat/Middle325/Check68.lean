import LocalWindowUnsat.Middle325.Data67
import LocalWindowUnsat.Middle325.Data68

/-! Kernel checks of segments 68-68 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok68 : andB (check start68 proof68) (cpOk (replay start68 proof68) start69) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
