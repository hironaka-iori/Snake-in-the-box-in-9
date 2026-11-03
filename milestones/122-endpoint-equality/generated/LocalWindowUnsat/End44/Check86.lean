import LocalWindowUnsat.End44.Data86
import LocalWindowUnsat.End44.Data87

/-! Kernel checks of segments 511-516 of `end44` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End44
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok511 : check start511 proof511 = true := by
  decide +kernel

theorem ok512 : check start512 proof512 = true := by
  decide +kernel

theorem ok513 : check start513 proof513 = true := by
  decide +kernel

theorem ok514 : check start514 proof514 = true := by
  decide +kernel

theorem ok515 : check start515 proof515 = true := by
  decide +kernel

theorem ok516 : andB (check start516 proof516) (cpOk (replay start516 proof516) start517) = true := by
  decide +kernel

end Snake9.LocalWindow.End44
