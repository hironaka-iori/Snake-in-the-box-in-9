import LocalWindowUnsat.ShareWindow144.Data266
import LocalWindowUnsat.ShareWindow144.Data267

/-! Kernel checks of segments 1061-1064 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1061 : check start1061 proof1061 = true := by
  decide +kernel

theorem ok1062 : check start1062 proof1062 = true := by
  decide +kernel

theorem ok1063 : check start1063 proof1063 = true := by
  decide +kernel

theorem ok1064 : andB (check start1064 proof1064) (cpOk (replay start1064 proof1064) start1065) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
