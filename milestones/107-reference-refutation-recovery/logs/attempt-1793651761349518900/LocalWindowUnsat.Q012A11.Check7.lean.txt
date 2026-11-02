import LocalWindowUnsat.Q012A11.Data6
import LocalWindowUnsat.Q012A11.Data7

/-! Kernel checks of segments 7-7 of `d012_a1_1` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Q012A11
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok7 : andB (check start7 proof7) (hasEmpty (replay start7 proof7) 1024) = true := by
  decide +kernel

end Snake9.LocalWindow.Q012A11
