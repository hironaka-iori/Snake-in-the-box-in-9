import Recovered111.LocalWindowUnsat.Middle325.Data171
import Recovered111.LocalWindowUnsat.Middle325.Data172

/-! Kernel checks of segments 172-172 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok172 : andB (check start172 proof172) (cpOk (replay start172 proof172) start173) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
