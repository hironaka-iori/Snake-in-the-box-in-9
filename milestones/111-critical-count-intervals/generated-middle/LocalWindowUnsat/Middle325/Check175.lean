import LocalWindowUnsat.Middle325.Data174
import LocalWindowUnsat.Middle325.Data175

/-! Kernel checks of segments 175-175 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok175 : check start175 proof175 = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
