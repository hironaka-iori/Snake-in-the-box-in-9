import LocalWindowUnsat.ShareWindow144.Data574
import LocalWindowUnsat.ShareWindow144.Data575

/-! Kernel checks of segments 2293-2296 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2293 : check start2293 proof2293 = true := by
  decide +kernel

theorem ok2294 : check start2294 proof2294 = true := by
  decide +kernel

theorem ok2295 : check start2295 proof2295 = true := by
  decide +kernel

theorem ok2296 : andB (check start2296 proof2296) (cpOk (replay start2296 proof2296) start2297) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
