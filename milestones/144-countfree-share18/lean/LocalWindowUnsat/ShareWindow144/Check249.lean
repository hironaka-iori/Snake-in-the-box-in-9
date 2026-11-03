import LocalWindowUnsat.ShareWindow144.Data249
import LocalWindowUnsat.ShareWindow144.Data250

/-! Kernel checks of segments 993-996 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok993 : check start993 proof993 = true := by
  decide +kernel

theorem ok994 : check start994 proof994 = true := by
  decide +kernel

theorem ok995 : check start995 proof995 = true := by
  decide +kernel

theorem ok996 : andB (check start996 proof996) (cpOk (replay start996 proof996) start997) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
