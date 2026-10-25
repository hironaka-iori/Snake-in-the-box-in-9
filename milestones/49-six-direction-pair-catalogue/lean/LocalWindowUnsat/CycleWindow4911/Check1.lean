import LocalWindowUnsat.CycleWindow4911.Data0
import LocalWindowUnsat.CycleWindow4911.Data1
import LocalWindowUnsat.CycleWindow4911.Data2
import LocalWindowUnsat.CycleWindow4911.Data3
import LocalWindowUnsat.CycleWindow4911.Data4
import LocalWindowUnsat.CycleWindow4911.Data5
import LocalWindowUnsat.CycleWindow4911.Data6

/-! Kernel checks of segments 1-6 of `cycle4911` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.CycleWindow4911
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok1 : check start1 proof1 = true := by
  decide +kernel

theorem ok2 : check start2 proof2 = true := by
  decide +kernel

theorem ok3 : check start3 proof3 = true := by
  decide +kernel

theorem ok4 : andB (check start4 proof4) (cpOk (replay start4 proof4) start5) = true := by
  decide +kernel

theorem ok5 : check start5 proof5 = true := by
  decide +kernel

theorem ok6 : check start6 proof6 = true := by
  decide +kernel

end Snake9.LocalWindow.CycleWindow4911
