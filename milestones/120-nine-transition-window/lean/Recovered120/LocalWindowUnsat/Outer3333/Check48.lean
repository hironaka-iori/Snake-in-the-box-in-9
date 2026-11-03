import Recovered120.LocalWindowUnsat.Outer3333.Data47
import Recovered120.LocalWindowUnsat.Outer3333.Data48

/-! Kernel checks of segments 48-48 of `outer3333` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Outer3333
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok48 : andB (check start48 proof48) (cpOk (replay start48 proof48) start49) = true := by
  decide +kernel

end Snake9.LocalWindow.Outer3333
