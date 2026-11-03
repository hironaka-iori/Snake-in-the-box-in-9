import LocalWindowUnsat.ShareWindow144.Data458
import LocalWindowUnsat.ShareWindow144.Data459

/-! Kernel checks of segments 1829-1832 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1829 : check start1829 proof1829 = true := by
  decide +kernel

theorem ok1830 : check start1830 proof1830 = true := by
  decide +kernel

theorem ok1831 : check start1831 proof1831 = true := by
  decide +kernel

theorem ok1832 : andB (check start1832 proof1832) (cpOk (replay start1832 proof1832) start1833) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
