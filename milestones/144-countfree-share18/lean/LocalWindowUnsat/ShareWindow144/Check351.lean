import LocalWindowUnsat.ShareWindow144.Data351
import LocalWindowUnsat.ShareWindow144.Data352

/-! Kernel checks of segments 1401-1404 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1401 : check start1401 proof1401 = true := by
  decide +kernel

theorem ok1402 : check start1402 proof1402 = true := by
  decide +kernel

theorem ok1403 : check start1403 proof1403 = true := by
  decide +kernel

theorem ok1404 : andB (check start1404 proof1404) (cpOk (replay start1404 proof1404) start1405) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
