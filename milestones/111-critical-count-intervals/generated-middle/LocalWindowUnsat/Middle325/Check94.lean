import LocalWindowUnsat.Middle325.Data93
import LocalWindowUnsat.Middle325.Data94

/-! Kernel checks of segments 94-94 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok94 : andB (check start94 proof94) (cpOk (replay start94 proof94) start95) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
