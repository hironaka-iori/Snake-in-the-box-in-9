import LocalWindowUnsat.CycleBase140.Data31
import LocalWindowUnsat.CycleBase140.Data32

/-! Kernel checks of segments 121-124 of `base140` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.CycleBase140
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok121 : check start121 proof121 = true := by
  decide +kernel

theorem ok122 : check start122 proof122 = true := by
  decide +kernel

theorem ok123 : check start123 proof123 = true := by
  decide +kernel

theorem ok124 : andB (check start124 proof124) (cpOk (replay start124 proof124) start125) = true := by
  decide +kernel

end Snake9.LocalWindow.CycleBase140
