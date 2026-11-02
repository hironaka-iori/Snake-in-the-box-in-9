import LocalWindowUnsat.Middle325R.Data26

/-! Kernel checks of segments 101-102 of `middle325r` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325R
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok101 : check start101 proof101 = true := by
  decide +kernel

theorem ok102 : andB (check start102 proof102) (hasEmpty (replay start102 proof102) 2048) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325R
