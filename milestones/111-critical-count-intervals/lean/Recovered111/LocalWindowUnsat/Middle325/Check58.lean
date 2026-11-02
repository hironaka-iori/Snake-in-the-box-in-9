import Recovered111.LocalWindowUnsat.Middle325.Data57
import Recovered111.LocalWindowUnsat.Middle325.Data58

/-! Kernel checks of segments 58-58 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok58 : andB (check start58 proof58) (cpOk (replay start58 proof58) start59) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
