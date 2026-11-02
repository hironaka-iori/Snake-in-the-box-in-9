import LocalWindowUnsat.Sum3142.Data2
import LocalWindowUnsat.Sum3142.Data3

/-! Kernel checks of segments 5-8 of `sum3142` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Sum3142
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok5 : check start5 proof5 = true := by
  decide +kernel

theorem ok6 : check start6 proof6 = true := by
  decide +kernel

theorem ok7 : check start7 proof7 = true := by
  decide +kernel

theorem ok8 : andB (check start8 proof8) (cpOk (replay start8 proof8) start9) = true := by
  decide +kernel

end Snake9.LocalWindow.Sum3142
