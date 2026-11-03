import LocalWindowUnsat.ShareWindow144.Data523
import LocalWindowUnsat.ShareWindow144.Data524

/-! Kernel checks of segments 2089-2092 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2089 : check start2089 proof2089 = true := by
  decide +kernel

theorem ok2090 : check start2090 proof2090 = true := by
  decide +kernel

theorem ok2091 : check start2091 proof2091 = true := by
  decide +kernel

theorem ok2092 : andB (check start2092 proof2092) (cpOk (replay start2092 proof2092) start2093) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
