import LocalWindowUnsat.ShareWindow144.Data585
import LocalWindowUnsat.ShareWindow144.Data586

/-! Kernel checks of segments 2337-2340 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2337 : check start2337 proof2337 = true := by
  decide +kernel

theorem ok2338 : check start2338 proof2338 = true := by
  decide +kernel

theorem ok2339 : check start2339 proof2339 = true := by
  decide +kernel

theorem ok2340 : andB (check start2340 proof2340) (cpOk (replay start2340 proof2340) start2341) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
