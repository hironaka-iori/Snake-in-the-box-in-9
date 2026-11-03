import LocalWindowUnsat.ShareWindow144.Data397
import LocalWindowUnsat.ShareWindow144.Data398

/-! Kernel checks of segments 1585-1588 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1585 : check start1585 proof1585 = true := by
  decide +kernel

theorem ok1586 : check start1586 proof1586 = true := by
  decide +kernel

theorem ok1587 : check start1587 proof1587 = true := by
  decide +kernel

theorem ok1588 : andB (check start1588 proof1588) (cpOk (replay start1588 proof1588) start1589) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
