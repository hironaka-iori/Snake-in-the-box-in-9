import LocalWindowUnsat.SixFour10.Data87
import LocalWindowUnsat.SixFour10.Data88

/-! Kernel checks of segments 517-522 of `four10` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.SixFour10
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok517 : check start517 proof517 = true := by
  decide +kernel

theorem ok518 : check start518 proof518 = true := by
  decide +kernel

theorem ok519 : check start519 proof519 = true := by
  decide +kernel

theorem ok520 : check start520 proof520 = true := by
  decide +kernel

theorem ok521 : check start521 proof521 = true := by
  decide +kernel

theorem ok522 : andB (check start522 proof522) (cpOk (replay start522 proof522) start523) = true := by
  decide +kernel

end Snake9.LocalWindow.SixFour10
