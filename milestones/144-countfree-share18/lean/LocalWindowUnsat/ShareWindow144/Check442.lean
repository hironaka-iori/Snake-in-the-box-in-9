import LocalWindowUnsat.ShareWindow144.Data442
import LocalWindowUnsat.ShareWindow144.Data443

/-! Kernel checks of segments 1765-1768 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1765 : check start1765 proof1765 = true := by
  decide +kernel

theorem ok1766 : check start1766 proof1766 = true := by
  decide +kernel

theorem ok1767 : check start1767 proof1767 = true := by
  decide +kernel

theorem ok1768 : andB (check start1768 proof1768) (cpOk (replay start1768 proof1768) start1769) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
