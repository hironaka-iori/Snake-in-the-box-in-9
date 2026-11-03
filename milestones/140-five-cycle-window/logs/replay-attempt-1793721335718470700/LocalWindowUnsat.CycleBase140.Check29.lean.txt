import LocalWindowUnsat.CycleBase140.Data29
import LocalWindowUnsat.CycleBase140.Data30

/-! Kernel checks of segments 113-116 of `base140` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.CycleBase140
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok113 : check start113 proof113 = true := by
  decide +kernel

theorem ok114 : check start114 proof114 = true := by
  decide +kernel

theorem ok115 : check start115 proof115 = true := by
  decide +kernel

theorem ok116 : andB (check start116 proof116) (cpOk (replay start116 proof116) start117) = true := by
  decide +kernel

end Snake9.LocalWindow.CycleBase140
