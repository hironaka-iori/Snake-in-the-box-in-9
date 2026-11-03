import LocalWindowUnsat.ShareWindow144.Data573
import LocalWindowUnsat.ShareWindow144.Data574

/-! Kernel checks of segments 2289-2292 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2289 : check start2289 proof2289 = true := by
  decide +kernel

theorem ok2290 : check start2290 proof2290 = true := by
  decide +kernel

theorem ok2291 : check start2291 proof2291 = true := by
  decide +kernel

theorem ok2292 : andB (check start2292 proof2292) (cpOk (replay start2292 proof2292) start2293) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
