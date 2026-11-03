import LocalWindowUnsat.ShareWindow144.Data426
import LocalWindowUnsat.ShareWindow144.Data427

/-! Kernel checks of segments 1701-1704 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1701 : check start1701 proof1701 = true := by
  decide +kernel

theorem ok1702 : check start1702 proof1702 = true := by
  decide +kernel

theorem ok1703 : check start1703 proof1703 = true := by
  decide +kernel

theorem ok1704 : andB (check start1704 proof1704) (cpOk (replay start1704 proof1704) start1705) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
