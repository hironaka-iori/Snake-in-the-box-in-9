import LocalWindowUnsat.Middle325.Data132
import LocalWindowUnsat.Middle325.Data133

/-! Kernel checks of segments 133-133 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok133 : check start133 proof133 = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
