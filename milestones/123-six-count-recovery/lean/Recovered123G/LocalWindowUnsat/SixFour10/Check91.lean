import Recovered123G.LocalWindowUnsat.SixFour10.Data91
import Recovered123G.LocalWindowUnsat.SixFour10.Data92

/-! Kernel checks of segments 541-546 of `four10` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.SixFour10
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok541 : check start541 proof541 = true := by
  decide +kernel

theorem ok542 : check start542 proof542 = true := by
  decide +kernel

theorem ok543 : check start543 proof543 = true := by
  decide +kernel

theorem ok544 : check start544 proof544 = true := by
  decide +kernel

theorem ok545 : check start545 proof545 = true := by
  decide +kernel

theorem ok546 : andB (check start546 proof546) (cpOk (replay start546 proof546) start547) = true := by
  decide +kernel

end Snake9.LocalWindow.SixFour10
