import LocalWindowUnsat.ShareWindow144.Data579
import LocalWindowUnsat.ShareWindow144.Data580

/-! Kernel checks of segments 2313-2316 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2313 : check start2313 proof2313 = true := by
  decide +kernel

theorem ok2314 : check start2314 proof2314 = true := by
  decide +kernel

theorem ok2315 : check start2315 proof2315 = true := by
  decide +kernel

theorem ok2316 : andB (check start2316 proof2316) (cpOk (replay start2316 proof2316) start2317) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
