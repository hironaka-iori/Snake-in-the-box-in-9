import Recovered120.LocalWindowUnsat.Outer3333.Data49
import Recovered120.LocalWindowUnsat.Outer3333.Data50

/-! Kernel checks of segments 50-50 of `outer3333` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Outer3333
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok50 : andB (check start50 proof50) (cpOk (replay start50 proof50) start51) = true := by
  decide +kernel

end Snake9.LocalWindow.Outer3333
