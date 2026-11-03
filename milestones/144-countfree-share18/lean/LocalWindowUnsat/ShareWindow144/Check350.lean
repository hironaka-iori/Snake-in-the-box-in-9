import LocalWindowUnsat.ShareWindow144.Data350
import LocalWindowUnsat.ShareWindow144.Data351

/-! Kernel checks of segments 1397-1400 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1397 : check start1397 proof1397 = true := by
  decide +kernel

theorem ok1398 : check start1398 proof1398 = true := by
  decide +kernel

theorem ok1399 : check start1399 proof1399 = true := by
  decide +kernel

theorem ok1400 : andB (check start1400 proof1400) (cpOk (replay start1400 proof1400) start1401) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
