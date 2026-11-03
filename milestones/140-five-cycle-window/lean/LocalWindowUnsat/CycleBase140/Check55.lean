import LocalWindowUnsat.CycleBase140.Data55
import LocalWindowUnsat.CycleBase140.Data56

/-! Kernel checks of segments 217-220 of `base140` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.CycleBase140
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok217 : check start217 proof217 = true := by
  decide +kernel

theorem ok218 : check start218 proof218 = true := by
  decide +kernel

theorem ok219 : check start219 proof219 = true := by
  decide +kernel

theorem ok220 : andB (check start220 proof220) (cpOk (replay start220 proof220) start221) = true := by
  decide +kernel

end Snake9.LocalWindow.CycleBase140
