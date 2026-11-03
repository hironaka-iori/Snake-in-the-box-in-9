import Recovered120.LocalWindowUnsat.Outer3333.Data52
import Recovered120.LocalWindowUnsat.Outer3333.Data53

/-! Kernel checks of segments 53-53 of `outer3333` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Outer3333
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok53 : check start53 proof53 = true := by
  decide +kernel

end Snake9.LocalWindow.Outer3333
