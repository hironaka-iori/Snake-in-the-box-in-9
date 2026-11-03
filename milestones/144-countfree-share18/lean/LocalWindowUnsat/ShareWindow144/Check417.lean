import LocalWindowUnsat.ShareWindow144.Data417
import LocalWindowUnsat.ShareWindow144.Data418

/-! Kernel checks of segments 1665-1668 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1665 : check start1665 proof1665 = true := by
  decide +kernel

theorem ok1666 : check start1666 proof1666 = true := by
  decide +kernel

theorem ok1667 : check start1667 proof1667 = true := by
  decide +kernel

theorem ok1668 : andB (check start1668 proof1668) (cpOk (replay start1668 proof1668) start1669) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
