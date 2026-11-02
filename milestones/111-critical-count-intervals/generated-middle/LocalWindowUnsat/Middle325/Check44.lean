import LocalWindowUnsat.Middle325.Data43
import LocalWindowUnsat.Middle325.Data44

/-! Kernel checks of segments 44-44 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok44 : andB (check start44 proof44) (cpOk (replay start44 proof44) start45) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
