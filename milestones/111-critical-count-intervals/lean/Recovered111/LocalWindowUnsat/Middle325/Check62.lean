import Recovered111.LocalWindowUnsat.Middle325.Data61
import Recovered111.LocalWindowUnsat.Middle325.Data62

/-! Kernel checks of segments 62-62 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok62 : andB (check start62 proof62) (cpOk (replay start62 proof62) start63) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
