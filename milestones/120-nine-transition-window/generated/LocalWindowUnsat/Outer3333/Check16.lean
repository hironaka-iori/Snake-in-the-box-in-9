import LocalWindowUnsat.Outer3333.Data15
import LocalWindowUnsat.Outer3333.Data16

/-! Kernel checks of segments 16-16 of `outer3333` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Outer3333
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok16 : andB (check start16 proof16) (cpOk (replay start16 proof16) start17) = true := by
  decide +kernel

end Snake9.LocalWindow.Outer3333
