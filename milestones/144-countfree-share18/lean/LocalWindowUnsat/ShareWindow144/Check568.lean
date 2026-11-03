import LocalWindowUnsat.ShareWindow144.Data568
import LocalWindowUnsat.ShareWindow144.Data569

/-! Kernel checks of segments 2269-2272 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2269 : check start2269 proof2269 = true := by
  decide +kernel

theorem ok2270 : check start2270 proof2270 = true := by
  decide +kernel

theorem ok2271 : check start2271 proof2271 = true := by
  decide +kernel

theorem ok2272 : andB (check start2272 proof2272) (cpOk (replay start2272 proof2272) start2273) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
