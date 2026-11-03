import LocalWindowUnsat.SixFour10.Data41
import LocalWindowUnsat.SixFour10.Data42

/-! Kernel checks of segments 241-246 of `four10` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.SixFour10
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok241 : check start241 proof241 = true := by
  decide +kernel

theorem ok242 : check start242 proof242 = true := by
  decide +kernel

theorem ok243 : check start243 proof243 = true := by
  decide +kernel

theorem ok244 : check start244 proof244 = true := by
  decide +kernel

theorem ok245 : check start245 proof245 = true := by
  decide +kernel

theorem ok246 : andB (check start246 proof246) (cpOk (replay start246 proof246) start247) = true := by
  decide +kernel

end Snake9.LocalWindow.SixFour10
