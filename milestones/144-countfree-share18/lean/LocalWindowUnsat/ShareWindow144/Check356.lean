import LocalWindowUnsat.ShareWindow144.Data356
import LocalWindowUnsat.ShareWindow144.Data357

/-! Kernel checks of segments 1421-1424 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1421 : check start1421 proof1421 = true := by
  decide +kernel

theorem ok1422 : check start1422 proof1422 = true := by
  decide +kernel

theorem ok1423 : check start1423 proof1423 = true := by
  decide +kernel

theorem ok1424 : andB (check start1424 proof1424) (cpOk (replay start1424 proof1424) start1425) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
