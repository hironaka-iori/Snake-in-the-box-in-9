import Recovered111.LocalWindowUnsat.Middle325.Data169
import Recovered111.LocalWindowUnsat.Middle325.Data170

/-! Kernel checks of segments 170-170 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok170 : andB (check start170 proof170) (cpOk (replay start170 proof170) start171) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
