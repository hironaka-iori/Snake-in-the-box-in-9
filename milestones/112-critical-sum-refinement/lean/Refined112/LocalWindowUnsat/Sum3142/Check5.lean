import Refined112.LocalWindowUnsat.Sum3142.Data5
import Refined112.LocalWindowUnsat.Sum3142.Data6

/-! Kernel checks of segments 17-20 of `sum3142` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Sum3142
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok17 : check start17 proof17 = true := by
  decide +kernel

theorem ok18 : check start18 proof18 = true := by
  decide +kernel

theorem ok19 : check start19 proof19 = true := by
  decide +kernel

theorem ok20 : andB (check start20 proof20) (cpOk (replay start20 proof20) start21) = true := by
  decide +kernel

end Snake9.LocalWindow.Sum3142
