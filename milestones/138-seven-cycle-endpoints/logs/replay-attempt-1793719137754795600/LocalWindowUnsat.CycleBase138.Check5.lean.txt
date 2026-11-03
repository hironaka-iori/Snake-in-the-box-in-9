import LocalWindowUnsat.CycleBase138.Data5

/-! Kernel checks of segments 17-18 of `base138` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.CycleBase138
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok17 : check start17 proof17 = true := by
  decide +kernel

theorem ok18 : andB (check start18 proof18) (hasEmpty (replay start18 proof18) 2048) = true := by
  decide +kernel

end Snake9.LocalWindow.CycleBase138
