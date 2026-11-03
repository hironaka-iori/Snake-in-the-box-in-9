import LocalWindowUnsat.ShareWindow144.Data473
import LocalWindowUnsat.ShareWindow144.Data474

/-! Kernel checks of segments 1889-1892 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1889 : check start1889 proof1889 = true := by
  decide +kernel

theorem ok1890 : check start1890 proof1890 = true := by
  decide +kernel

theorem ok1891 : check start1891 proof1891 = true := by
  decide +kernel

theorem ok1892 : andB (check start1892 proof1892) (cpOk (replay start1892 proof1892) start1893) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
