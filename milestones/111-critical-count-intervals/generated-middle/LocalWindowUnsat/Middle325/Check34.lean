import LocalWindowUnsat.Middle325.Data33
import LocalWindowUnsat.Middle325.Data34

/-! Kernel checks of segments 34-34 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok34 : andB (check start34 proof34) (cpOk (replay start34 proof34) start35) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
