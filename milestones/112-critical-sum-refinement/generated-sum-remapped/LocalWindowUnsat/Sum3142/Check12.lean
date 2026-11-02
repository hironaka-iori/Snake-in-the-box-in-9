import LocalWindowUnsat.Sum3142.Data12
import LocalWindowUnsat.Sum3142.Data13

/-! Kernel checks of segments 45-48 of `sum3142` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Sum3142
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok45 : check start45 proof45 = true := by
  decide +kernel

theorem ok46 : check start46 proof46 = true := by
  decide +kernel

theorem ok47 : check start47 proof47 = true := by
  decide +kernel

theorem ok48 : andB (check start48 proof48) (cpOk (replay start48 proof48) start49) = true := by
  decide +kernel

end Snake9.LocalWindow.Sum3142
