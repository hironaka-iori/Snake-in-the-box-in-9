import Recovered123G.LocalWindowUnsat.SixFour10.Data88
import Recovered123G.LocalWindowUnsat.SixFour10.Data89

/-! Kernel checks of segments 523-528 of `four10` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.SixFour10
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok523 : check start523 proof523 = true := by
  decide +kernel

theorem ok524 : check start524 proof524 = true := by
  decide +kernel

theorem ok525 : check start525 proof525 = true := by
  decide +kernel

theorem ok526 : check start526 proof526 = true := by
  decide +kernel

theorem ok527 : check start527 proof527 = true := by
  decide +kernel

theorem ok528 : andB (check start528 proof528) (cpOk (replay start528 proof528) start529) = true := by
  decide +kernel

end Snake9.LocalWindow.SixFour10
