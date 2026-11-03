import Recovered120.LocalWindowUnsat.Outer3333.Data48
import Recovered120.LocalWindowUnsat.Outer3333.Data49

/-! Kernel checks of segments 49-49 of `outer3333` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Outer3333
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok49 : check start49 proof49 = true := by
  decide +kernel

end Snake9.LocalWindow.Outer3333
