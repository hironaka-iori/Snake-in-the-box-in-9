import LocalWindowUnsat.ShareWindow144.Data309
import LocalWindowUnsat.ShareWindow144.Data310

/-! Kernel checks of segments 1233-1236 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1233 : check start1233 proof1233 = true := by
  decide +kernel

theorem ok1234 : check start1234 proof1234 = true := by
  decide +kernel

theorem ok1235 : check start1235 proof1235 = true := by
  decide +kernel

theorem ok1236 : andB (check start1236 proof1236) (cpOk (replay start1236 proof1236) start1237) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
