import LocalWindowUnsat.ShareWindow144.Data120
import LocalWindowUnsat.ShareWindow144.Data121

/-! Kernel checks of segments 477-480 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok477 : check start477 proof477 = true := by
  decide +kernel

theorem ok478 : check start478 proof478 = true := by
  decide +kernel

theorem ok479 : check start479 proof479 = true := by
  decide +kernel

theorem ok480 : andB (check start480 proof480) (cpOk (replay start480 proof480) start481) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
