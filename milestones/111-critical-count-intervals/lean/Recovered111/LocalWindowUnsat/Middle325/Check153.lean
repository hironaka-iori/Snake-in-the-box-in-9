import Recovered111.LocalWindowUnsat.Middle325.Data152
import Recovered111.LocalWindowUnsat.Middle325.Data153

/-! Kernel checks of segments 153-153 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok153 : check start153 proof153 = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
