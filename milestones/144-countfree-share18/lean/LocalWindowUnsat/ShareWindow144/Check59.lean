import LocalWindowUnsat.ShareWindow144.Data59
import LocalWindowUnsat.ShareWindow144.Data60

/-! Kernel checks of segments 233-236 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok233 : check start233 proof233 = true := by
  decide +kernel

theorem ok234 : check start234 proof234 = true := by
  decide +kernel

theorem ok235 : check start235 proof235 = true := by
  decide +kernel

theorem ok236 : andB (check start236 proof236) (cpOk (replay start236 proof236) start237) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
