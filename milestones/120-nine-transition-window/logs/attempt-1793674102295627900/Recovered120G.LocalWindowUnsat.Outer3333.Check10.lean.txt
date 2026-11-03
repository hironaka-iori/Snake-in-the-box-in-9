import Recovered120G.LocalWindowUnsat.Outer3333.Data10

/-! Kernel checks of segments 55-57 of `outer3333` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Outer3333
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok55 : check start55 proof55 = true := by
  decide +kernel

theorem ok56 : check start56 proof56 = true := by
  decide +kernel

theorem ok57 : andB (check start57 proof57) (hasEmpty (replay start57 proof57) 2048) = true := by
  decide +kernel

end Snake9.LocalWindow.Outer3333
