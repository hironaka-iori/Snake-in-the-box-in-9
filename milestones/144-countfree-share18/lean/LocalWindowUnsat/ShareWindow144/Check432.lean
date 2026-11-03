import LocalWindowUnsat.ShareWindow144.Data432
import LocalWindowUnsat.ShareWindow144.Data433

/-! Kernel checks of segments 1725-1728 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1725 : check start1725 proof1725 = true := by
  decide +kernel

theorem ok1726 : check start1726 proof1726 = true := by
  decide +kernel

theorem ok1727 : check start1727 proof1727 = true := by
  decide +kernel

theorem ok1728 : andB (check start1728 proof1728) (cpOk (replay start1728 proof1728) start1729) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
