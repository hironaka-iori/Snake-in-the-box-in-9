import LocalWindowUnsat.FourRun22.Data0
import LocalWindowUnsat.FourRun22.Data1

/-! Kernel checks of segments 1-1 of `four22` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.FourRun22
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok1 : andB (check start1 proof1) (hasEmpty (replay start1 proof1) 64) = true := by
  decide +kernel

end Snake9.LocalWindow.FourRun22
