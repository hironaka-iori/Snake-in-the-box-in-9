import Recovered123G.LocalWindowUnsat.SixFour10.Data47
import Recovered123G.LocalWindowUnsat.SixFour10.Data48

/-! Kernel checks of segments 277-282 of `four10` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.SixFour10
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok277 : check start277 proof277 = true := by
  decide +kernel

theorem ok278 : check start278 proof278 = true := by
  decide +kernel

theorem ok279 : check start279 proof279 = true := by
  decide +kernel

theorem ok280 : check start280 proof280 = true := by
  decide +kernel

theorem ok281 : check start281 proof281 = true := by
  decide +kernel

theorem ok282 : andB (check start282 proof282) (cpOk (replay start282 proof282) start283) = true := by
  decide +kernel

end Snake9.LocalWindow.SixFour10
