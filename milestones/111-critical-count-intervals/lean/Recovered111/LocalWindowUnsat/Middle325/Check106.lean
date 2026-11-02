import Recovered111.LocalWindowUnsat.Middle325.Data105
import Recovered111.LocalWindowUnsat.Middle325.Data106

/-! Kernel checks of segments 106-106 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok106 : andB (check start106 proof106) (cpOk (replay start106 proof106) start107) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
