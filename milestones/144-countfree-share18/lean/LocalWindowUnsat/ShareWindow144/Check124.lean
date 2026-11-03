import LocalWindowUnsat.ShareWindow144.Data124
import LocalWindowUnsat.ShareWindow144.Data125

/-! Kernel checks of segments 493-496 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok493 : check start493 proof493 = true := by
  decide +kernel

theorem ok494 : check start494 proof494 = true := by
  decide +kernel

theorem ok495 : check start495 proof495 = true := by
  decide +kernel

theorem ok496 : andB (check start496 proof496) (cpOk (replay start496 proof496) start497) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
