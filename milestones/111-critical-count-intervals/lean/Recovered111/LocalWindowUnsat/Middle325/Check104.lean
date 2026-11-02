import Recovered111.LocalWindowUnsat.Middle325.Data103
import Recovered111.LocalWindowUnsat.Middle325.Data104

/-! Kernel checks of segments 104-104 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok104 : andB (check start104 proof104) (cpOk (replay start104 proof104) start105) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
