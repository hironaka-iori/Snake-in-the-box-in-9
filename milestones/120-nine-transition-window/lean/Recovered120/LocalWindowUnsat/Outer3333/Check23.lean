import Recovered120.LocalWindowUnsat.Outer3333.Data22
import Recovered120.LocalWindowUnsat.Outer3333.Data23

/-! Kernel checks of segments 23-23 of `outer3333` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Outer3333
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok23 : check start23 proof23 = true := by
  decide +kernel

end Snake9.LocalWindow.Outer3333
