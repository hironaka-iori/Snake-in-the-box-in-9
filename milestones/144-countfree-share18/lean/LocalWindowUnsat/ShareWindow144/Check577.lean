import LocalWindowUnsat.ShareWindow144.Data577
import LocalWindowUnsat.ShareWindow144.Data578

/-! Kernel checks of segments 2305-2308 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2305 : check start2305 proof2305 = true := by
  decide +kernel

theorem ok2306 : check start2306 proof2306 = true := by
  decide +kernel

theorem ok2307 : check start2307 proof2307 = true := by
  decide +kernel

theorem ok2308 : andB (check start2308 proof2308) (cpOk (replay start2308 proof2308) start2309) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
