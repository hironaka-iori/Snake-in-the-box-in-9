import LocalWindowUnsat.ShareWindow144.Data444
import LocalWindowUnsat.ShareWindow144.Data445

/-! Kernel checks of segments 1773-1776 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1773 : check start1773 proof1773 = true := by
  decide +kernel

theorem ok1774 : check start1774 proof1774 = true := by
  decide +kernel

theorem ok1775 : check start1775 proof1775 = true := by
  decide +kernel

theorem ok1776 : andB (check start1776 proof1776) (cpOk (replay start1776 proof1776) start1777) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
