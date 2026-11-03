import LocalWindowUnsat.ShareWindow144.Data450
import LocalWindowUnsat.ShareWindow144.Data451

/-! Kernel checks of segments 1797-1800 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1797 : check start1797 proof1797 = true := by
  decide +kernel

theorem ok1798 : check start1798 proof1798 = true := by
  decide +kernel

theorem ok1799 : check start1799 proof1799 = true := by
  decide +kernel

theorem ok1800 : andB (check start1800 proof1800) (cpOk (replay start1800 proof1800) start1801) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
