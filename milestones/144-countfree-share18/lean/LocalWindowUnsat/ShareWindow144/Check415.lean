import LocalWindowUnsat.ShareWindow144.Data415
import LocalWindowUnsat.ShareWindow144.Data416

/-! Kernel checks of segments 1657-1660 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1657 : check start1657 proof1657 = true := by
  decide +kernel

theorem ok1658 : check start1658 proof1658 = true := by
  decide +kernel

theorem ok1659 : check start1659 proof1659 = true := by
  decide +kernel

theorem ok1660 : andB (check start1660 proof1660) (cpOk (replay start1660 proof1660) start1661) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
