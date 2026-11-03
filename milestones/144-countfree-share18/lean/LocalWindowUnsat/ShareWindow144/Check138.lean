import LocalWindowUnsat.ShareWindow144.Data138
import LocalWindowUnsat.ShareWindow144.Data139

/-! Kernel checks of segments 549-552 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok549 : check start549 proof549 = true := by
  decide +kernel

theorem ok550 : check start550 proof550 = true := by
  decide +kernel

theorem ok551 : check start551 proof551 = true := by
  decide +kernel

theorem ok552 : andB (check start552 proof552) (cpOk (replay start552 proof552) start553) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
