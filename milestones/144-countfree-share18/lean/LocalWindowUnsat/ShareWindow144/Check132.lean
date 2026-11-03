import LocalWindowUnsat.ShareWindow144.Data132
import LocalWindowUnsat.ShareWindow144.Data133

/-! Kernel checks of segments 525-528 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok525 : check start525 proof525 = true := by
  decide +kernel

theorem ok526 : check start526 proof526 = true := by
  decide +kernel

theorem ok527 : check start527 proof527 = true := by
  decide +kernel

theorem ok528 : andB (check start528 proof528) (cpOk (replay start528 proof528) start529) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
