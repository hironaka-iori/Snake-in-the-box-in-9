import LocalWindowUnsat.CycleBase140.Data52
import LocalWindowUnsat.CycleBase140.Data53

/-! Kernel checks of segments 205-208 of `base140` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.CycleBase140
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok205 : check start205 proof205 = true := by
  decide +kernel

theorem ok206 : check start206 proof206 = true := by
  decide +kernel

theorem ok207 : check start207 proof207 = true := by
  decide +kernel

theorem ok208 : andB (check start208 proof208) (cpOk (replay start208 proof208) start209) = true := by
  decide +kernel

end Snake9.LocalWindow.CycleBase140
