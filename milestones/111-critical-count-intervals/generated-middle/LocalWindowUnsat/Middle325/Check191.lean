import LocalWindowUnsat.Middle325.Data190
import LocalWindowUnsat.Middle325.Data191

/-! Kernel checks of segments 191-191 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok191 : check start191 proof191 = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
