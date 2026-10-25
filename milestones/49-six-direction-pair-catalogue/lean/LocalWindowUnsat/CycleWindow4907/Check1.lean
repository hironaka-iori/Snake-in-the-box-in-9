import LocalWindowUnsat.CycleWindow4907.Data0
import LocalWindowUnsat.CycleWindow4907.Data1
import LocalWindowUnsat.CycleWindow4907.Data2
import LocalWindowUnsat.CycleWindow4907.Data3
import LocalWindowUnsat.CycleWindow4907.Data4

/-! Kernel checks of segments 1-4 of `cycle4907` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.CycleWindow4907
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok1 : check start1 proof1 = true := by
  decide +kernel

theorem ok2 : check start2 proof2 = true := by
  decide +kernel

theorem ok3 : check start3 proof3 = true := by
  decide +kernel

theorem ok4 : andB (check start4 proof4) (hasEmpty (replay start4 proof4) 1024) = true := by
  decide +kernel

end Snake9.LocalWindow.CycleWindow4907
