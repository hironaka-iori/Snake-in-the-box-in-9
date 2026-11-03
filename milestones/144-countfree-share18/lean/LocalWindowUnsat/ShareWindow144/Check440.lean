import LocalWindowUnsat.ShareWindow144.Data440
import LocalWindowUnsat.ShareWindow144.Data441

/-! Kernel checks of segments 1757-1760 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1757 : check start1757 proof1757 = true := by
  decide +kernel

theorem ok1758 : check start1758 proof1758 = true := by
  decide +kernel

theorem ok1759 : check start1759 proof1759 = true := by
  decide +kernel

theorem ok1760 : andB (check start1760 proof1760) (cpOk (replay start1760 proof1760) start1761) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
