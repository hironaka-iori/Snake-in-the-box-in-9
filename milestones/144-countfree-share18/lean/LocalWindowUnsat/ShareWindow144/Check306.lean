import LocalWindowUnsat.ShareWindow144.Data306
import LocalWindowUnsat.ShareWindow144.Data307

/-! Kernel checks of segments 1221-1224 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1221 : check start1221 proof1221 = true := by
  decide +kernel

theorem ok1222 : check start1222 proof1222 = true := by
  decide +kernel

theorem ok1223 : check start1223 proof1223 = true := by
  decide +kernel

theorem ok1224 : andB (check start1224 proof1224) (cpOk (replay start1224 proof1224) start1225) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
