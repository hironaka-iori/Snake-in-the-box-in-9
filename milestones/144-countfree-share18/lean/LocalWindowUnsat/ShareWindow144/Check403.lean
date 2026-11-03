import LocalWindowUnsat.ShareWindow144.Data403
import LocalWindowUnsat.ShareWindow144.Data404

/-! Kernel checks of segments 1609-1612 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1609 : check start1609 proof1609 = true := by
  decide +kernel

theorem ok1610 : check start1610 proof1610 = true := by
  decide +kernel

theorem ok1611 : check start1611 proof1611 = true := by
  decide +kernel

theorem ok1612 : andB (check start1612 proof1612) (cpOk (replay start1612 proof1612) start1613) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
