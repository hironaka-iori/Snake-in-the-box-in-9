import LocalWindowUnsat.Middle325.Data112
import LocalWindowUnsat.Middle325.Data113

/-! Kernel checks of segments 113-113 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok113 : check start113 proof113 = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
