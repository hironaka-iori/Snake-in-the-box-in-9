import Recovered111.LocalWindowUnsat.Middle325.Data39
import Recovered111.LocalWindowUnsat.Middle325.Data40

/-! Kernel checks of segments 40-40 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok40 : andB (check start40 proof40) (cpOk (replay start40 proof40) start41) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
