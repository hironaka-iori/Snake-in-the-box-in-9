import Recovered123G.LocalWindowUnsat.SixFour10.Data83
import Recovered123G.LocalWindowUnsat.SixFour10.Data84

/-! Kernel checks of segments 493-498 of `four10` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.SixFour10
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok493 : check start493 proof493 = true := by
  decide +kernel

theorem ok494 : check start494 proof494 = true := by
  decide +kernel

theorem ok495 : check start495 proof495 = true := by
  decide +kernel

theorem ok496 : check start496 proof496 = true := by
  decide +kernel

theorem ok497 : check start497 proof497 = true := by
  decide +kernel

theorem ok498 : andB (check start498 proof498) (cpOk (replay start498 proof498) start499) = true := by
  decide +kernel

end Snake9.LocalWindow.SixFour10
