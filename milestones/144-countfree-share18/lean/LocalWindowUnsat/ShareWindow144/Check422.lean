import LocalWindowUnsat.ShareWindow144.Data422
import LocalWindowUnsat.ShareWindow144.Data423

/-! Kernel checks of segments 1685-1688 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1685 : check start1685 proof1685 = true := by
  decide +kernel

theorem ok1686 : check start1686 proof1686 = true := by
  decide +kernel

theorem ok1687 : check start1687 proof1687 = true := by
  decide +kernel

theorem ok1688 : andB (check start1688 proof1688) (cpOk (replay start1688 proof1688) start1689) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
