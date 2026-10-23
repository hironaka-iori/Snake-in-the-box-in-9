import LocalWindowUnsat.FourRun0.Data60
import LocalWindowUnsat.FourRun0.Data61
import LocalWindowUnsat.FourRun0.Data62
import LocalWindowUnsat.FourRun0.Data63

/-! Kernel checks of segments 61-63 of `four0` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.FourRun0
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok61 : check start61 proof61 = true := by
  decide +kernel

theorem ok62 : check start62 proof62 = true := by
  decide +kernel

theorem ok63 : andB (check start63 proof63) (hasEmpty (replay start63 proof63) 4096) = true := by
  decide +kernel

end Snake9.LocalWindow.FourRun0
