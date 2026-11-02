import Recovered111.LocalWindowUnsat.Middle325.Data85
import Recovered111.LocalWindowUnsat.Middle325.Data86

/-! Kernel checks of segments 86-86 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok86 : andB (check start86 proof86) (cpOk (replay start86 proof86) start87) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
