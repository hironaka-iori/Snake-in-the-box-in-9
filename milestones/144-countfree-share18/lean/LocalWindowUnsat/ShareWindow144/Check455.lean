import LocalWindowUnsat.ShareWindow144.Data455
import LocalWindowUnsat.ShareWindow144.Data456

/-! Kernel checks of segments 1817-1820 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1817 : check start1817 proof1817 = true := by
  decide +kernel

theorem ok1818 : check start1818 proof1818 = true := by
  decide +kernel

theorem ok1819 : check start1819 proof1819 = true := by
  decide +kernel

theorem ok1820 : andB (check start1820 proof1820) (cpOk (replay start1820 proof1820) start1821) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
