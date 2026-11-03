import LocalWindowUnsat.Outer3333.Data12
import LocalWindowUnsat.Outer3333.Data13

/-! Kernel checks of segments 13-13 of `outer3333` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Outer3333
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok13 : check start13 proof13 = true := by
  decide +kernel

end Snake9.LocalWindow.Outer3333
