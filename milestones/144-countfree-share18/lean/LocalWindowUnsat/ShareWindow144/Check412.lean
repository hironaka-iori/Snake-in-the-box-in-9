import LocalWindowUnsat.ShareWindow144.Data412
import LocalWindowUnsat.ShareWindow144.Data413

/-! Kernel checks of segments 1645-1648 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1645 : check start1645 proof1645 = true := by
  decide +kernel

theorem ok1646 : check start1646 proof1646 = true := by
  decide +kernel

theorem ok1647 : check start1647 proof1647 = true := by
  decide +kernel

theorem ok1648 : andB (check start1648 proof1648) (cpOk (replay start1648 proof1648) start1649) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
