import Recovered120.LocalWindowUnsat.Outer3333.Data44
import Recovered120.LocalWindowUnsat.Outer3333.Data45

/-! Kernel checks of segments 45-45 of `outer3333` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Outer3333
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok45 : check start45 proof45 = true := by
  decide +kernel

end Snake9.LocalWindow.Outer3333
