import LocalWindowUnsat.Middle325.Data95
import LocalWindowUnsat.Middle325.Data96

/-! Kernel checks of segments 96-96 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok96 : andB (check start96 proof96) (cpOk (replay start96 proof96) start97) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
