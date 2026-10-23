import LocalWindowUnsat.FourRun0.Data30
import LocalWindowUnsat.FourRun0.Data31
import LocalWindowUnsat.FourRun0.Data32
import LocalWindowUnsat.FourRun0.Data33
import LocalWindowUnsat.FourRun0.Data34
import LocalWindowUnsat.FourRun0.Data35
import LocalWindowUnsat.FourRun0.Data36

/-! Kernel checks of segments 31-36 of `four0` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.FourRun0
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok31 : check start31 proof31 = true := by
  decide +kernel

theorem ok32 : andB (check start32 proof32) (cpOk (replay start32 proof32) start33) = true := by
  decide +kernel

theorem ok33 : check start33 proof33 = true := by
  decide +kernel

theorem ok34 : check start34 proof34 = true := by
  decide +kernel

theorem ok35 : check start35 proof35 = true := by
  decide +kernel

theorem ok36 : andB (check start36 proof36) (cpOk (replay start36 proof36) start37) = true := by
  decide +kernel

end Snake9.LocalWindow.FourRun0
