import LocalWindowUnsat.ShareWindow144.Data131
import LocalWindowUnsat.ShareWindow144.Data132

/-! Kernel checks of segments 521-524 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok521 : check start521 proof521 = true := by
  decide +kernel

theorem ok522 : check start522 proof522 = true := by
  decide +kernel

theorem ok523 : check start523 proof523 = true := by
  decide +kernel

theorem ok524 : andB (check start524 proof524) (cpOk (replay start524 proof524) start525) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
