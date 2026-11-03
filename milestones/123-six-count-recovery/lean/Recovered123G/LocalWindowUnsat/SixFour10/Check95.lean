import Recovered123G.LocalWindowUnsat.SixFour10.Data95
import Recovered123G.LocalWindowUnsat.SixFour10.Data96

/-! Kernel checks of segments 565-570 of `four10` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.SixFour10
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok565 : check start565 proof565 = true := by
  decide +kernel

theorem ok566 : check start566 proof566 = true := by
  decide +kernel

theorem ok567 : check start567 proof567 = true := by
  decide +kernel

theorem ok568 : check start568 proof568 = true := by
  decide +kernel

theorem ok569 : check start569 proof569 = true := by
  decide +kernel

theorem ok570 : andB (check start570 proof570) (cpOk (replay start570 proof570) start571) = true := by
  decide +kernel

end Snake9.LocalWindow.SixFour10
