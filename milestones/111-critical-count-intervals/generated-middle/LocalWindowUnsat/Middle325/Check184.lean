import LocalWindowUnsat.Middle325.Data183
import LocalWindowUnsat.Middle325.Data184

/-! Kernel checks of segments 184-184 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok184 : andB (check start184 proof184) (cpOk (replay start184 proof184) start185) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
