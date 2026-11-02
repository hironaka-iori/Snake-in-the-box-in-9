import Recovered111.LocalWindowUnsat.Middle325.Data155
import Recovered111.LocalWindowUnsat.Middle325.Data156

/-! Kernel checks of segments 156-156 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok156 : andB (check start156 proof156) (cpOk (replay start156 proof156) start157) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
