import LocalWindowUnsat.End44.Data101
import LocalWindowUnsat.End44.Data102

/-! Kernel checks of segments 601-606 of `end44` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End44
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok601 : check start601 proof601 = true := by
  decide +kernel

theorem ok602 : check start602 proof602 = true := by
  decide +kernel

theorem ok603 : check start603 proof603 = true := by
  decide +kernel

theorem ok604 : check start604 proof604 = true := by
  decide +kernel

theorem ok605 : check start605 proof605 = true := by
  decide +kernel

theorem ok606 : andB (check start606 proof606) (cpOk (replay start606 proof606) start607) = true := by
  decide +kernel

end Snake9.LocalWindow.End44
