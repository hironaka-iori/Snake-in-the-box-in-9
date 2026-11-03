import LocalWindowUnsat.ShareWindow144.Data135
import LocalWindowUnsat.ShareWindow144.Data136

/-! Kernel checks of segments 537-540 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok537 : check start537 proof537 = true := by
  decide +kernel

theorem ok538 : check start538 proof538 = true := by
  decide +kernel

theorem ok539 : check start539 proof539 = true := by
  decide +kernel

theorem ok540 : andB (check start540 proof540) (cpOk (replay start540 proof540) start541) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
