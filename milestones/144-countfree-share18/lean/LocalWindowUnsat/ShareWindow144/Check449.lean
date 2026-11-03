import LocalWindowUnsat.ShareWindow144.Data449
import LocalWindowUnsat.ShareWindow144.Data450

/-! Kernel checks of segments 1793-1796 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1793 : check start1793 proof1793 = true := by
  decide +kernel

theorem ok1794 : check start1794 proof1794 = true := by
  decide +kernel

theorem ok1795 : check start1795 proof1795 = true := by
  decide +kernel

theorem ok1796 : andB (check start1796 proof1796) (cpOk (replay start1796 proof1796) start1797) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
