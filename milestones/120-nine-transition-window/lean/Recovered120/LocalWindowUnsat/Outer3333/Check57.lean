import Recovered120.LocalWindowUnsat.Outer3333.Data56
import Recovered120.LocalWindowUnsat.Outer3333.Data57

/-! Kernel checks of segments 57-57 of `outer3333` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Outer3333
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok57 : andB (check start57 proof57) (hasEmpty (replay start57 proof57) 2048) = true := by
  decide +kernel

end Snake9.LocalWindow.Outer3333
