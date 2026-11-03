import LocalWindowUnsat.SixFour10.Data77
import LocalWindowUnsat.SixFour10.Data78

/-! Kernel checks of segments 457-462 of `four10` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.SixFour10
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok457 : check start457 proof457 = true := by
  decide +kernel

theorem ok458 : check start458 proof458 = true := by
  decide +kernel

theorem ok459 : check start459 proof459 = true := by
  decide +kernel

theorem ok460 : check start460 proof460 = true := by
  decide +kernel

theorem ok461 : check start461 proof461 = true := by
  decide +kernel

theorem ok462 : andB (check start462 proof462) (cpOk (replay start462 proof462) start463) = true := by
  decide +kernel

end Snake9.LocalWindow.SixFour10
