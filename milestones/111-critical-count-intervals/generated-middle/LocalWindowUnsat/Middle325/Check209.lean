import LocalWindowUnsat.Middle325.Data208
import LocalWindowUnsat.Middle325.Data209

/-! Kernel checks of segments 209-209 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok209 : andB (check start209 proof209) (hasEmpty (replay start209 proof209) 2048) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
