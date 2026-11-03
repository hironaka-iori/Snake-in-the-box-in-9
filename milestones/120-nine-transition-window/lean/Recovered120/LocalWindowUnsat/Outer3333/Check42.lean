import Recovered120.LocalWindowUnsat.Outer3333.Data41
import Recovered120.LocalWindowUnsat.Outer3333.Data42

/-! Kernel checks of segments 42-42 of `outer3333` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Outer3333
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok42 : andB (check start42 proof42) (cpOk (replay start42 proof42) start43) = true := by
  decide +kernel

end Snake9.LocalWindow.Outer3333
