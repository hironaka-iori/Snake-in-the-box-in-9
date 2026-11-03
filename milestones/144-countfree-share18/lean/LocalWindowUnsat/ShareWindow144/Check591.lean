import LocalWindowUnsat.ShareWindow144.Data591
import LocalWindowUnsat.ShareWindow144.Data592

/-! Kernel checks of segments 2361-2364 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2361 : check start2361 proof2361 = true := by
  decide +kernel

theorem ok2362 : check start2362 proof2362 = true := by
  decide +kernel

theorem ok2363 : check start2363 proof2363 = true := by
  decide +kernel

theorem ok2364 : andB (check start2364 proof2364) (cpOk (replay start2364 proof2364) start2365) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
