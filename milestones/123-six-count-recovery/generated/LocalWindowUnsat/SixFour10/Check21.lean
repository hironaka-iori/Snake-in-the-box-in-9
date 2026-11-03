import LocalWindowUnsat.SixFour10.Data21
import LocalWindowUnsat.SixFour10.Data22

/-! Kernel checks of segments 121-126 of `four10` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.SixFour10
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok121 : check start121 proof121 = true := by
  decide +kernel

theorem ok122 : check start122 proof122 = true := by
  decide +kernel

theorem ok123 : check start123 proof123 = true := by
  decide +kernel

theorem ok124 : check start124 proof124 = true := by
  decide +kernel

theorem ok125 : check start125 proof125 = true := by
  decide +kernel

theorem ok126 : andB (check start126 proof126) (cpOk (replay start126 proof126) start127) = true := by
  decide +kernel

end Snake9.LocalWindow.SixFour10
