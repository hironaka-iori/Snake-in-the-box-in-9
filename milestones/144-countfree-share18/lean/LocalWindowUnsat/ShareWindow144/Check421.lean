import LocalWindowUnsat.ShareWindow144.Data421
import LocalWindowUnsat.ShareWindow144.Data422

/-! Kernel checks of segments 1681-1684 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1681 : check start1681 proof1681 = true := by
  decide +kernel

theorem ok1682 : check start1682 proof1682 = true := by
  decide +kernel

theorem ok1683 : check start1683 proof1683 = true := by
  decide +kernel

theorem ok1684 : andB (check start1684 proof1684) (cpOk (replay start1684 proof1684) start1685) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
