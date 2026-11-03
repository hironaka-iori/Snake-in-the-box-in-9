import Recovered123G.LocalWindowUnsat.SixFour10.Data79
import Recovered123G.LocalWindowUnsat.SixFour10.Data80

/-! Kernel checks of segments 469-474 of `four10` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.SixFour10
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok469 : check start469 proof469 = true := by
  decide +kernel

theorem ok470 : check start470 proof470 = true := by
  decide +kernel

theorem ok471 : check start471 proof471 = true := by
  decide +kernel

theorem ok472 : check start472 proof472 = true := by
  decide +kernel

theorem ok473 : check start473 proof473 = true := by
  decide +kernel

theorem ok474 : andB (check start474 proof474) (cpOk (replay start474 proof474) start475) = true := by
  decide +kernel

end Snake9.LocalWindow.SixFour10
