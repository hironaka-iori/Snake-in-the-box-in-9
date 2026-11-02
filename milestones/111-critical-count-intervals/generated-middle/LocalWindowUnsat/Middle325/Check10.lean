import LocalWindowUnsat.Middle325.Data9
import LocalWindowUnsat.Middle325.Data10

/-! Kernel checks of segments 10-10 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok10 : andB (check start10 proof10) (cpOk (replay start10 proof10) start11) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
