import LocalWindowUnsat.CycleWindow4918.Data18
import LocalWindowUnsat.CycleWindow4918.Data19

/-! Kernel checks of segments 19-19 of `cycle4918` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.CycleWindow4918
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok19 : andB (check start19 proof19) (hasEmpty (replay start19 proof19) 2048) = true := by
  decide +kernel

end Snake9.LocalWindow.CycleWindow4918
