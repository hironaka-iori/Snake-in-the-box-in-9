import LocalWindowUnsat.SixFour10.Data90
import LocalWindowUnsat.SixFour10.Data91

/-! Kernel checks of segments 535-540 of `four10` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.SixFour10
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok535 : check start535 proof535 = true := by
  decide +kernel

theorem ok536 : check start536 proof536 = true := by
  decide +kernel

theorem ok537 : check start537 proof537 = true := by
  decide +kernel

theorem ok538 : check start538 proof538 = true := by
  decide +kernel

theorem ok539 : check start539 proof539 = true := by
  decide +kernel

theorem ok540 : andB (check start540 proof540) (cpOk (replay start540 proof540) start541) = true := by
  decide +kernel

end Snake9.LocalWindow.SixFour10
