import LocalWindowUnsat.End44.Data92
import LocalWindowUnsat.End44.Data93

/-! Kernel checks of segments 547-552 of `end44` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End44
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok547 : check start547 proof547 = true := by
  decide +kernel

theorem ok548 : check start548 proof548 = true := by
  decide +kernel

theorem ok549 : check start549 proof549 = true := by
  decide +kernel

theorem ok550 : check start550 proof550 = true := by
  decide +kernel

theorem ok551 : check start551 proof551 = true := by
  decide +kernel

theorem ok552 : andB (check start552 proof552) (cpOk (replay start552 proof552) start553) = true := by
  decide +kernel

end Snake9.LocalWindow.End44
