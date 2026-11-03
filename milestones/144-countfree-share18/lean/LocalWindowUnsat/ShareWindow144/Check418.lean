import LocalWindowUnsat.ShareWindow144.Data418
import LocalWindowUnsat.ShareWindow144.Data419

/-! Kernel checks of segments 1669-1672 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1669 : check start1669 proof1669 = true := by
  decide +kernel

theorem ok1670 : check start1670 proof1670 = true := by
  decide +kernel

theorem ok1671 : check start1671 proof1671 = true := by
  decide +kernel

theorem ok1672 : andB (check start1672 proof1672) (cpOk (replay start1672 proof1672) start1673) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
