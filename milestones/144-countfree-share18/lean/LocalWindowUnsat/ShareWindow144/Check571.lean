import LocalWindowUnsat.ShareWindow144.Data571
import LocalWindowUnsat.ShareWindow144.Data572

/-! Kernel checks of segments 2281-2284 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2281 : check start2281 proof2281 = true := by
  decide +kernel

theorem ok2282 : check start2282 proof2282 = true := by
  decide +kernel

theorem ok2283 : check start2283 proof2283 = true := by
  decide +kernel

theorem ok2284 : andB (check start2284 proof2284) (cpOk (replay start2284 proof2284) start2285) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
