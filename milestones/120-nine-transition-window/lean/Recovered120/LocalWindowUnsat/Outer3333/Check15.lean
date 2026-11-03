import Recovered120.LocalWindowUnsat.Outer3333.Data14
import Recovered120.LocalWindowUnsat.Outer3333.Data15

/-! Kernel checks of segments 15-15 of `outer3333` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Outer3333
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok15 : check start15 proof15 = true := by
  decide +kernel

end Snake9.LocalWindow.Outer3333
