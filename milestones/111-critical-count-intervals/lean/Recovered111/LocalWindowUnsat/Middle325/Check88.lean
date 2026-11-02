import Recovered111.LocalWindowUnsat.Middle325.Data87
import Recovered111.LocalWindowUnsat.Middle325.Data88

/-! Kernel checks of segments 88-88 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok88 : andB (check start88 proof88) (cpOk (replay start88 proof88) start89) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
