import LocalWindowUnsat.End44.Data88
import LocalWindowUnsat.End44.Data89

/-! Kernel checks of segments 523-528 of `end44` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End44
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok523 : check start523 proof523 = true := by
  decide +kernel

theorem ok524 : check start524 proof524 = true := by
  decide +kernel

theorem ok525 : check start525 proof525 = true := by
  decide +kernel

theorem ok526 : check start526 proof526 = true := by
  decide +kernel

theorem ok527 : check start527 proof527 = true := by
  decide +kernel

theorem ok528 : andB (check start528 proof528) (cpOk (replay start528 proof528) start529) = true := by
  decide +kernel

end Snake9.LocalWindow.End44
