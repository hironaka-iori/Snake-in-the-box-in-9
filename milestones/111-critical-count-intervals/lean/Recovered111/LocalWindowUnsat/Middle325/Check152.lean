import Recovered111.LocalWindowUnsat.Middle325.Data151
import Recovered111.LocalWindowUnsat.Middle325.Data152

/-! Kernel checks of segments 152-152 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok152 : andB (check start152 proof152) (cpOk (replay start152 proof152) start153) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
