import LocalWindowUnsat.Outer3333.Data1
import LocalWindowUnsat.Outer3333.Data2

/-! Kernel checks of segments 2-2 of `outer3333` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Outer3333
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok2 : andB (check start2 proof2) (cpOk (replay start2 proof2) start3) = true := by
  decide +kernel

end Snake9.LocalWindow.Outer3333
