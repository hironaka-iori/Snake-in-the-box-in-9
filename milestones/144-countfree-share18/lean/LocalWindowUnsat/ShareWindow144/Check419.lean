import LocalWindowUnsat.ShareWindow144.Data419
import LocalWindowUnsat.ShareWindow144.Data420

/-! Kernel checks of segments 1673-1676 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1673 : check start1673 proof1673 = true := by
  decide +kernel

theorem ok1674 : check start1674 proof1674 = true := by
  decide +kernel

theorem ok1675 : check start1675 proof1675 = true := by
  decide +kernel

theorem ok1676 : andB (check start1676 proof1676) (cpOk (replay start1676 proof1676) start1677) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
