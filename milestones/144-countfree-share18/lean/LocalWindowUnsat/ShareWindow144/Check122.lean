import LocalWindowUnsat.ShareWindow144.Data122
import LocalWindowUnsat.ShareWindow144.Data123

/-! Kernel checks of segments 485-488 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok485 : check start485 proof485 = true := by
  decide +kernel

theorem ok486 : check start486 proof486 = true := by
  decide +kernel

theorem ok487 : check start487 proof487 = true := by
  decide +kernel

theorem ok488 : andB (check start488 proof488) (cpOk (replay start488 proof488) start489) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
