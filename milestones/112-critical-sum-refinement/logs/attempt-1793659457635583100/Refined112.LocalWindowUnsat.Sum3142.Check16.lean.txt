import Refined112.LocalWindowUnsat.Sum3142.Data16

/-! Kernel checks of segments 61-61 of `sum3142` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Sum3142
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok61 : andB (check start61 proof61) (hasEmpty (replay start61 proof61) 2048) = true := by
  decide +kernel

end Snake9.LocalWindow.Sum3142
