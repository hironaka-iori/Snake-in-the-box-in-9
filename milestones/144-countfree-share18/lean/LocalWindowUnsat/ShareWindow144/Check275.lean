import LocalWindowUnsat.ShareWindow144.Data275
import LocalWindowUnsat.ShareWindow144.Data276

/-! Kernel checks of segments 1097-1100 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1097 : check start1097 proof1097 = true := by
  decide +kernel

theorem ok1098 : check start1098 proof1098 = true := by
  decide +kernel

theorem ok1099 : check start1099 proof1099 = true := by
  decide +kernel

theorem ok1100 : andB (check start1100 proof1100) (cpOk (replay start1100 proof1100) start1101) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
