import LocalWindowUnsat.Middle325.Data75
import LocalWindowUnsat.Middle325.Data76

/-! Kernel checks of segments 76-76 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok76 : andB (check start76 proof76) (cpOk (replay start76 proof76) start77) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
