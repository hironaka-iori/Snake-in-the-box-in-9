import LocalWindowUnsat.Middle325.Data111
import LocalWindowUnsat.Middle325.Data112

/-! Kernel checks of segments 112-112 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok112 : andB (check start112 proof112) (cpOk (replay start112 proof112) start113) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
