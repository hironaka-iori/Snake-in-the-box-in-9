import LocalWindowUnsat.SixFour10.Data82
import LocalWindowUnsat.SixFour10.Data83

/-! Kernel checks of segments 487-492 of `four10` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.SixFour10
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok487 : check start487 proof487 = true := by
  decide +kernel

theorem ok488 : check start488 proof488 = true := by
  decide +kernel

theorem ok489 : check start489 proof489 = true := by
  decide +kernel

theorem ok490 : check start490 proof490 = true := by
  decide +kernel

theorem ok491 : check start491 proof491 = true := by
  decide +kernel

theorem ok492 : andB (check start492 proof492) (cpOk (replay start492 proof492) start493) = true := by
  decide +kernel

end Snake9.LocalWindow.SixFour10
