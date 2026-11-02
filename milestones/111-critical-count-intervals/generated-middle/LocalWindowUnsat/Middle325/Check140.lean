import LocalWindowUnsat.Middle325.Data139
import LocalWindowUnsat.Middle325.Data140

/-! Kernel checks of segments 140-140 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok140 : andB (check start140 proof140) (cpOk (replay start140 proof140) start141) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
