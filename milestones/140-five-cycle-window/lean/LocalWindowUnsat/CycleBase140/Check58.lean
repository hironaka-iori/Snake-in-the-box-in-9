import LocalWindowUnsat.CycleBase140.Data58

/-! Kernel checks of segments 229-229 of `base140` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.CycleBase140
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok229 : andB (check start229 proof229) (hasEmpty (replay start229 proof229) 4096) = true := by
  decide +kernel

end Snake9.LocalWindow.CycleBase140
