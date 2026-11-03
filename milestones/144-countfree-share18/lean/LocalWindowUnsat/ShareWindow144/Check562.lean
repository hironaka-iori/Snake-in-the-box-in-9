import LocalWindowUnsat.ShareWindow144.Data562
import LocalWindowUnsat.ShareWindow144.Data563

/-! Kernel checks of segments 2245-2248 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2245 : check start2245 proof2245 = true := by
  decide +kernel

theorem ok2246 : check start2246 proof2246 = true := by
  decide +kernel

theorem ok2247 : check start2247 proof2247 = true := by
  decide +kernel

theorem ok2248 : andB (check start2248 proof2248) (cpOk (replay start2248 proof2248) start2249) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
