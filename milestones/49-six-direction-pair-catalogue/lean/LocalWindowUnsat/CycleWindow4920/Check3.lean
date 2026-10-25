import LocalWindowUnsat.CycleWindow4920.Data12
import LocalWindowUnsat.CycleWindow4920.Data13
import LocalWindowUnsat.CycleWindow4920.Data14
import LocalWindowUnsat.CycleWindow4920.Data15

/-! Kernel checks of segments 13-15 of `cycle4920` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.CycleWindow4920
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok13 : check start13 proof13 = true := by
  decide +kernel

theorem ok14 : check start14 proof14 = true := by
  decide +kernel

theorem ok15 : andB (check start15 proof15) (hasEmpty (replay start15 proof15) 1024) = true := by
  decide +kernel

end Snake9.LocalWindow.CycleWindow4920
