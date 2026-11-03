import LocalWindowUnsat.SixFour10.Data55
import LocalWindowUnsat.SixFour10.Data56

/-! Kernel checks of segments 325-330 of `four10` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.SixFour10
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok325 : check start325 proof325 = true := by
  decide +kernel

theorem ok326 : check start326 proof326 = true := by
  decide +kernel

theorem ok327 : check start327 proof327 = true := by
  decide +kernel

theorem ok328 : check start328 proof328 = true := by
  decide +kernel

theorem ok329 : check start329 proof329 = true := by
  decide +kernel

theorem ok330 : andB (check start330 proof330) (cpOk (replay start330 proof330) start331) = true := by
  decide +kernel

end Snake9.LocalWindow.SixFour10
