import LocalWindowUnsat.ShareWindow144.Data587
import LocalWindowUnsat.ShareWindow144.Data588

/-! Kernel checks of segments 2345-2348 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2345 : check start2345 proof2345 = true := by
  decide +kernel

theorem ok2346 : check start2346 proof2346 = true := by
  decide +kernel

theorem ok2347 : check start2347 proof2347 = true := by
  decide +kernel

theorem ok2348 : andB (check start2348 proof2348) (cpOk (replay start2348 proof2348) start2349) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
