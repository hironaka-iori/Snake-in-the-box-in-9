import LocalWindowUnsat.ShareWindow144.Data447
import LocalWindowUnsat.ShareWindow144.Data448

/-! Kernel checks of segments 1785-1788 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1785 : check start1785 proof1785 = true := by
  decide +kernel

theorem ok1786 : check start1786 proof1786 = true := by
  decide +kernel

theorem ok1787 : check start1787 proof1787 = true := by
  decide +kernel

theorem ok1788 : andB (check start1788 proof1788) (cpOk (replay start1788 proof1788) start1789) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
