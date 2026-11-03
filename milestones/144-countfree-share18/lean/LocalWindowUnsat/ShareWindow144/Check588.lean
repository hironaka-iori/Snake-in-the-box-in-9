import LocalWindowUnsat.ShareWindow144.Data588
import LocalWindowUnsat.ShareWindow144.Data589

/-! Kernel checks of segments 2349-2352 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2349 : check start2349 proof2349 = true := by
  decide +kernel

theorem ok2350 : check start2350 proof2350 = true := by
  decide +kernel

theorem ok2351 : check start2351 proof2351 = true := by
  decide +kernel

theorem ok2352 : andB (check start2352 proof2352) (cpOk (replay start2352 proof2352) start2353) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
