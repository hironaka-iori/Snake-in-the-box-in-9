import Recovered111.LocalWindowUnsat.Middle325.Data63
import Recovered111.LocalWindowUnsat.Middle325.Data64

/-! Kernel checks of segments 64-64 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok64 : andB (check start64 proof64) (cpOk (replay start64 proof64) start65) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
