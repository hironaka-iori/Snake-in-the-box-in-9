import LocalWindowUnsat.SixFour10.Data35
import LocalWindowUnsat.SixFour10.Data36

/-! Kernel checks of segments 205-210 of `four10` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.SixFour10
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok205 : check start205 proof205 = true := by
  decide +kernel

theorem ok206 : check start206 proof206 = true := by
  decide +kernel

theorem ok207 : check start207 proof207 = true := by
  decide +kernel

theorem ok208 : check start208 proof208 = true := by
  decide +kernel

theorem ok209 : check start209 proof209 = true := by
  decide +kernel

theorem ok210 : andB (check start210 proof210) (cpOk (replay start210 proof210) start211) = true := by
  decide +kernel

end Snake9.LocalWindow.SixFour10
