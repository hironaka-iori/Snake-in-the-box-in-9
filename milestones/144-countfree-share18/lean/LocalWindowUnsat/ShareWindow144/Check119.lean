import LocalWindowUnsat.ShareWindow144.Data119
import LocalWindowUnsat.ShareWindow144.Data120

/-! Kernel checks of segments 473-476 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok473 : check start473 proof473 = true := by
  decide +kernel

theorem ok474 : check start474 proof474 = true := by
  decide +kernel

theorem ok475 : check start475 proof475 = true := by
  decide +kernel

theorem ok476 : andB (check start476 proof476) (cpOk (replay start476 proof476) start477) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
