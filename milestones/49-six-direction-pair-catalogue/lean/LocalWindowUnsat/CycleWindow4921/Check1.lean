import LocalWindowUnsat.CycleWindow4921.Data0
import LocalWindowUnsat.CycleWindow4921.Data1
import LocalWindowUnsat.CycleWindow4921.Data2
import LocalWindowUnsat.CycleWindow4921.Data3

/-! Kernel checks of segments 1-3 of `cycle4921` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.CycleWindow4921
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok1 : check start1 proof1 = true := by
  decide +kernel

theorem ok2 : check start2 proof2 = true := by
  decide +kernel

theorem ok3 : andB (check start3 proof3) (hasEmpty (replay start3 proof3) 512) = true := by
  decide +kernel

end Snake9.LocalWindow.CycleWindow4921
