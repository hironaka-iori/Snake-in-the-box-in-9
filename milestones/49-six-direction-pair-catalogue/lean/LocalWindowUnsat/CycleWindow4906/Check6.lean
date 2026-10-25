import LocalWindowUnsat.CycleWindow4906.Data30
import LocalWindowUnsat.CycleWindow4906.Data31
import LocalWindowUnsat.CycleWindow4906.Data32
import LocalWindowUnsat.CycleWindow4906.Data33

/-! Kernel checks of segments 31-33 of `cycle4906` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.CycleWindow4906
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok31 : check start31 proof31 = true := by
  decide +kernel

theorem ok32 : andB (check start32 proof32) (cpOk (replay start32 proof32) start33) = true := by
  decide +kernel

theorem ok33 : andB (check start33 proof33) (hasEmpty (replay start33 proof33) 2048) = true := by
  decide +kernel

end Snake9.LocalWindow.CycleWindow4906
