import LocalWindowUnsat.ShareWindow144.Data404
import LocalWindowUnsat.ShareWindow144.Data405

/-! Kernel checks of segments 1613-1616 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1613 : check start1613 proof1613 = true := by
  decide +kernel

theorem ok1614 : check start1614 proof1614 = true := by
  decide +kernel

theorem ok1615 : check start1615 proof1615 = true := by
  decide +kernel

theorem ok1616 : andB (check start1616 proof1616) (cpOk (replay start1616 proof1616) start1617) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
