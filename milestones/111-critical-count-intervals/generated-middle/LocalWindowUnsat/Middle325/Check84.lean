import LocalWindowUnsat.Middle325.Data83
import LocalWindowUnsat.Middle325.Data84

/-! Kernel checks of segments 84-84 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok84 : andB (check start84 proof84) (cpOk (replay start84 proof84) start85) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
