import Recovered123G.LocalWindowUnsat.SixFour10.Data48
import Recovered123G.LocalWindowUnsat.SixFour10.Data49

/-! Kernel checks of segments 283-288 of `four10` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.SixFour10
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok283 : check start283 proof283 = true := by
  decide +kernel

theorem ok284 : check start284 proof284 = true := by
  decide +kernel

theorem ok285 : check start285 proof285 = true := by
  decide +kernel

theorem ok286 : check start286 proof286 = true := by
  decide +kernel

theorem ok287 : check start287 proof287 = true := by
  decide +kernel

theorem ok288 : andB (check start288 proof288) (cpOk (replay start288 proof288) start289) = true := by
  decide +kernel

end Snake9.LocalWindow.SixFour10
