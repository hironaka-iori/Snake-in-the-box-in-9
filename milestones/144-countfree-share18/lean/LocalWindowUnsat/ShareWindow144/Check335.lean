import LocalWindowUnsat.ShareWindow144.Data335
import LocalWindowUnsat.ShareWindow144.Data336

/-! Kernel checks of segments 1337-1340 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1337 : check start1337 proof1337 = true := by
  decide +kernel

theorem ok1338 : check start1338 proof1338 = true := by
  decide +kernel

theorem ok1339 : check start1339 proof1339 = true := by
  decide +kernel

theorem ok1340 : andB (check start1340 proof1340) (cpOk (replay start1340 proof1340) start1341) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
