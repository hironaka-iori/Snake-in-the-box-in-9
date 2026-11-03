import Recovered120.LocalWindowUnsat.Outer3333.Data38
import Recovered120.LocalWindowUnsat.Outer3333.Data39

/-! Kernel checks of segments 39-39 of `outer3333` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Outer3333
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok39 : check start39 proof39 = true := by
  decide +kernel

end Snake9.LocalWindow.Outer3333
