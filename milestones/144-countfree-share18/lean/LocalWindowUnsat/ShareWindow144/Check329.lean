import LocalWindowUnsat.ShareWindow144.Data329
import LocalWindowUnsat.ShareWindow144.Data330

/-! Kernel checks of segments 1313-1316 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1313 : check start1313 proof1313 = true := by
  decide +kernel

theorem ok1314 : check start1314 proof1314 = true := by
  decide +kernel

theorem ok1315 : check start1315 proof1315 = true := by
  decide +kernel

theorem ok1316 : andB (check start1316 proof1316) (cpOk (replay start1316 proof1316) start1317) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
