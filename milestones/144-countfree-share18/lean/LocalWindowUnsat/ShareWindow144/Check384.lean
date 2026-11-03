import LocalWindowUnsat.ShareWindow144.Data384
import LocalWindowUnsat.ShareWindow144.Data385

/-! Kernel checks of segments 1533-1536 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1533 : check start1533 proof1533 = true := by
  decide +kernel

theorem ok1534 : check start1534 proof1534 = true := by
  decide +kernel

theorem ok1535 : check start1535 proof1535 = true := by
  decide +kernel

theorem ok1536 : andB (check start1536 proof1536) (cpOk (replay start1536 proof1536) start1537) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
