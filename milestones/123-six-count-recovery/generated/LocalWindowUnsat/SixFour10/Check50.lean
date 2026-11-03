import LocalWindowUnsat.SixFour10.Data50
import LocalWindowUnsat.SixFour10.Data51

/-! Kernel checks of segments 295-300 of `four10` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.SixFour10
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok295 : check start295 proof295 = true := by
  decide +kernel

theorem ok296 : check start296 proof296 = true := by
  decide +kernel

theorem ok297 : check start297 proof297 = true := by
  decide +kernel

theorem ok298 : check start298 proof298 = true := by
  decide +kernel

theorem ok299 : check start299 proof299 = true := by
  decide +kernel

theorem ok300 : andB (check start300 proof300) (cpOk (replay start300 proof300) start301) = true := by
  decide +kernel

end Snake9.LocalWindow.SixFour10
