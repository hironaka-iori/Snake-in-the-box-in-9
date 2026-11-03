import LocalWindowUnsat.ShareWindow144.Data162
import LocalWindowUnsat.ShareWindow144.Data163

/-! Kernel checks of segments 645-648 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok645 : check start645 proof645 = true := by
  decide +kernel

theorem ok646 : check start646 proof646 = true := by
  decide +kernel

theorem ok647 : check start647 proof647 = true := by
  decide +kernel

theorem ok648 : andB (check start648 proof648) (cpOk (replay start648 proof648) start649) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
