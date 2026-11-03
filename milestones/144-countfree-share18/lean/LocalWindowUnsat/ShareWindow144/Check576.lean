import LocalWindowUnsat.ShareWindow144.Data576
import LocalWindowUnsat.ShareWindow144.Data577

/-! Kernel checks of segments 2301-2304 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2301 : check start2301 proof2301 = true := by
  decide +kernel

theorem ok2302 : check start2302 proof2302 = true := by
  decide +kernel

theorem ok2303 : check start2303 proof2303 = true := by
  decide +kernel

theorem ok2304 : andB (check start2304 proof2304) (cpOk (replay start2304 proof2304) start2305) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
