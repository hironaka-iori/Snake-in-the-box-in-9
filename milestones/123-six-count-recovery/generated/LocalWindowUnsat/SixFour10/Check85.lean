import LocalWindowUnsat.SixFour10.Data85
import LocalWindowUnsat.SixFour10.Data86

/-! Kernel checks of segments 505-510 of `four10` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.SixFour10
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok505 : check start505 proof505 = true := by
  decide +kernel

theorem ok506 : check start506 proof506 = true := by
  decide +kernel

theorem ok507 : check start507 proof507 = true := by
  decide +kernel

theorem ok508 : check start508 proof508 = true := by
  decide +kernel

theorem ok509 : check start509 proof509 = true := by
  decide +kernel

theorem ok510 : andB (check start510 proof510) (cpOk (replay start510 proof510) start511) = true := by
  decide +kernel

end Snake9.LocalWindow.SixFour10
