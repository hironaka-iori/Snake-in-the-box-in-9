import LocalWindowUnsat.ShareWindow144.Data439
import LocalWindowUnsat.ShareWindow144.Data440

/-! Kernel checks of segments 1753-1756 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1753 : check start1753 proof1753 = true := by
  decide +kernel

theorem ok1754 : check start1754 proof1754 = true := by
  decide +kernel

theorem ok1755 : check start1755 proof1755 = true := by
  decide +kernel

theorem ok1756 : andB (check start1756 proof1756) (cpOk (replay start1756 proof1756) start1757) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
