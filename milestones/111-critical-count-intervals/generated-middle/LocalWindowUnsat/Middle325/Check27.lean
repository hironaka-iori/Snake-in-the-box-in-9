import LocalWindowUnsat.Middle325.Data26
import LocalWindowUnsat.Middle325.Data27

/-! Kernel checks of segments 27-27 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok27 : check start27 proof27 = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
