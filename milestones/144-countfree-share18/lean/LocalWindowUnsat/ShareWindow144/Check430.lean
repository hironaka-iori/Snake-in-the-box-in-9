import LocalWindowUnsat.ShareWindow144.Data430
import LocalWindowUnsat.ShareWindow144.Data431

/-! Kernel checks of segments 1717-1720 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1717 : check start1717 proof1717 = true := by
  decide +kernel

theorem ok1718 : check start1718 proof1718 = true := by
  decide +kernel

theorem ok1719 : check start1719 proof1719 = true := by
  decide +kernel

theorem ok1720 : andB (check start1720 proof1720) (cpOk (replay start1720 proof1720) start1721) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
