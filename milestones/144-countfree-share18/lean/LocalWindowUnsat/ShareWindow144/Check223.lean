import LocalWindowUnsat.ShareWindow144.Data223
import LocalWindowUnsat.ShareWindow144.Data224

/-! Kernel checks of segments 889-892 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok889 : check start889 proof889 = true := by
  decide +kernel

theorem ok890 : check start890 proof890 = true := by
  decide +kernel

theorem ok891 : check start891 proof891 = true := by
  decide +kernel

theorem ok892 : andB (check start892 proof892) (cpOk (replay start892 proof892) start893) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
