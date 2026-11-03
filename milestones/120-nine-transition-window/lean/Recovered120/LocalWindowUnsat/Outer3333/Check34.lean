import Recovered120.LocalWindowUnsat.Outer3333.Data33
import Recovered120.LocalWindowUnsat.Outer3333.Data34

/-! Kernel checks of segments 34-34 of `outer3333` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Outer3333
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok34 : andB (check start34 proof34) (cpOk (replay start34 proof34) start35) = true := by
  decide +kernel

end Snake9.LocalWindow.Outer3333
