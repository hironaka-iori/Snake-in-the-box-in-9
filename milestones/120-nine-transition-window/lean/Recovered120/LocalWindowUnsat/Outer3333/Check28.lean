import Recovered120.LocalWindowUnsat.Outer3333.Data27
import Recovered120.LocalWindowUnsat.Outer3333.Data28

/-! Kernel checks of segments 28-28 of `outer3333` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Outer3333
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok28 : andB (check start28 proof28) (cpOk (replay start28 proof28) start29) = true := by
  decide +kernel

end Snake9.LocalWindow.Outer3333
