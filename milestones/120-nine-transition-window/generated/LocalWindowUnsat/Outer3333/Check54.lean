import LocalWindowUnsat.Outer3333.Data53
import LocalWindowUnsat.Outer3333.Data54

/-! Kernel checks of segments 54-54 of `outer3333` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Outer3333
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok54 : andB (check start54 proof54) (cpOk (replay start54 proof54) start55) = true := by
  decide +kernel

end Snake9.LocalWindow.Outer3333
