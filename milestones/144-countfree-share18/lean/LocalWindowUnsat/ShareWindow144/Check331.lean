import LocalWindowUnsat.ShareWindow144.Data331
import LocalWindowUnsat.ShareWindow144.Data332

/-! Kernel checks of segments 1321-1324 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1321 : check start1321 proof1321 = true := by
  decide +kernel

theorem ok1322 : check start1322 proof1322 = true := by
  decide +kernel

theorem ok1323 : check start1323 proof1323 = true := by
  decide +kernel

theorem ok1324 : andB (check start1324 proof1324) (cpOk (replay start1324 proof1324) start1325) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
