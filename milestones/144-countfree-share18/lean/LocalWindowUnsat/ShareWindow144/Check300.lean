import LocalWindowUnsat.ShareWindow144.Data300
import LocalWindowUnsat.ShareWindow144.Data301

/-! Kernel checks of segments 1197-1200 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1197 : check start1197 proof1197 = true := by
  decide +kernel

theorem ok1198 : check start1198 proof1198 = true := by
  decide +kernel

theorem ok1199 : check start1199 proof1199 = true := by
  decide +kernel

theorem ok1200 : andB (check start1200 proof1200) (cpOk (replay start1200 proof1200) start1201) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
