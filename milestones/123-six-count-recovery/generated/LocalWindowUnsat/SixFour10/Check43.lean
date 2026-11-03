import LocalWindowUnsat.SixFour10.Data43
import LocalWindowUnsat.SixFour10.Data44

/-! Kernel checks of segments 253-258 of `four10` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.SixFour10
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok253 : check start253 proof253 = true := by
  decide +kernel

theorem ok254 : check start254 proof254 = true := by
  decide +kernel

theorem ok255 : check start255 proof255 = true := by
  decide +kernel

theorem ok256 : check start256 proof256 = true := by
  decide +kernel

theorem ok257 : check start257 proof257 = true := by
  decide +kernel

theorem ok258 : andB (check start258 proof258) (cpOk (replay start258 proof258) start259) = true := by
  decide +kernel

end Snake9.LocalWindow.SixFour10
