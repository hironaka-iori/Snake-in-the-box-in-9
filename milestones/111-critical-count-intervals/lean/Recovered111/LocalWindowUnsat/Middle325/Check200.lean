import Recovered111.LocalWindowUnsat.Middle325.Data199
import Recovered111.LocalWindowUnsat.Middle325.Data200

/-! Kernel checks of segments 200-200 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok200 : andB (check start200 proof200) (cpOk (replay start200 proof200) start201) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
