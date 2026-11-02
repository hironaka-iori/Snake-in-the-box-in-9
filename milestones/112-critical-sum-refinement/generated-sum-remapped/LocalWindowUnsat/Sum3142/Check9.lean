import LocalWindowUnsat.Sum3142.Data9
import LocalWindowUnsat.Sum3142.Data10

/-! Kernel checks of segments 33-36 of `sum3142` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Sum3142
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok33 : check start33 proof33 = true := by
  decide +kernel

theorem ok34 : check start34 proof34 = true := by
  decide +kernel

theorem ok35 : check start35 proof35 = true := by
  decide +kernel

theorem ok36 : andB (check start36 proof36) (cpOk (replay start36 proof36) start37) = true := by
  decide +kernel

end Snake9.LocalWindow.Sum3142
