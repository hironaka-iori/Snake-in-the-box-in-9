import Recovered111.LocalWindowUnsat.Middle325.Data69
import Recovered111.LocalWindowUnsat.Middle325.Data70

/-! Kernel checks of segments 70-70 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok70 : andB (check start70 proof70) (cpOk (replay start70 proof70) start71) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
