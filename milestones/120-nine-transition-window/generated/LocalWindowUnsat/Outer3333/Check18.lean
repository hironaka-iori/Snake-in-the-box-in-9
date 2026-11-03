import LocalWindowUnsat.Outer3333.Data17
import LocalWindowUnsat.Outer3333.Data18

/-! Kernel checks of segments 18-18 of `outer3333` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Outer3333
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok18 : andB (check start18 proof18) (cpOk (replay start18 proof18) start19) = true := by
  decide +kernel

end Snake9.LocalWindow.Outer3333
