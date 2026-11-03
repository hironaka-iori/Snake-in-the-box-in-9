import LocalWindowUnsat.SixFour10.Data15
import LocalWindowUnsat.SixFour10.Data16

/-! Kernel checks of segments 85-90 of `four10` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.SixFour10
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok85 : check start85 proof85 = true := by
  decide +kernel

theorem ok86 : check start86 proof86 = true := by
  decide +kernel

theorem ok87 : check start87 proof87 = true := by
  decide +kernel

theorem ok88 : check start88 proof88 = true := by
  decide +kernel

theorem ok89 : check start89 proof89 = true := by
  decide +kernel

theorem ok90 : andB (check start90 proof90) (cpOk (replay start90 proof90) start91) = true := by
  decide +kernel

end Snake9.LocalWindow.SixFour10
