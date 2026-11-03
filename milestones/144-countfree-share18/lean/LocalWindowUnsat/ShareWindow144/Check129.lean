import LocalWindowUnsat.ShareWindow144.Data129
import LocalWindowUnsat.ShareWindow144.Data130

/-! Kernel checks of segments 513-516 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok513 : check start513 proof513 = true := by
  decide +kernel

theorem ok514 : check start514 proof514 = true := by
  decide +kernel

theorem ok515 : check start515 proof515 = true := by
  decide +kernel

theorem ok516 : andB (check start516 proof516) (cpOk (replay start516 proof516) start517) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
