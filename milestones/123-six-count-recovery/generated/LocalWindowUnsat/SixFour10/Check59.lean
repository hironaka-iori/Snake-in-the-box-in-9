import LocalWindowUnsat.SixFour10.Data59
import LocalWindowUnsat.SixFour10.Data60

/-! Kernel checks of segments 349-354 of `four10` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.SixFour10
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok349 : check start349 proof349 = true := by
  decide +kernel

theorem ok350 : check start350 proof350 = true := by
  decide +kernel

theorem ok351 : check start351 proof351 = true := by
  decide +kernel

theorem ok352 : check start352 proof352 = true := by
  decide +kernel

theorem ok353 : check start353 proof353 = true := by
  decide +kernel

theorem ok354 : andB (check start354 proof354) (cpOk (replay start354 proof354) start355) = true := by
  decide +kernel

end Snake9.LocalWindow.SixFour10
