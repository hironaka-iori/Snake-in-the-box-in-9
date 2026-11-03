import Recovered123G.LocalWindowUnsat.SixFour10.Data37
import Recovered123G.LocalWindowUnsat.SixFour10.Data38

/-! Kernel checks of segments 217-222 of `four10` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.SixFour10
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok217 : check start217 proof217 = true := by
  decide +kernel

theorem ok218 : check start218 proof218 = true := by
  decide +kernel

theorem ok219 : check start219 proof219 = true := by
  decide +kernel

theorem ok220 : check start220 proof220 = true := by
  decide +kernel

theorem ok221 : check start221 proof221 = true := by
  decide +kernel

theorem ok222 : andB (check start222 proof222) (cpOk (replay start222 proof222) start223) = true := by
  decide +kernel

end Snake9.LocalWindow.SixFour10
