import LocalWindowUnsat.Middle325.Data131
import LocalWindowUnsat.Middle325.Data132

/-! Kernel checks of segments 132-132 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok132 : andB (check start132 proof132) (cpOk (replay start132 proof132) start133) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
