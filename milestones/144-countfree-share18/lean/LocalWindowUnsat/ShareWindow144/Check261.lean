import LocalWindowUnsat.ShareWindow144.Data261
import LocalWindowUnsat.ShareWindow144.Data262

/-! Kernel checks of segments 1041-1044 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1041 : check start1041 proof1041 = true := by
  decide +kernel

theorem ok1042 : check start1042 proof1042 = true := by
  decide +kernel

theorem ok1043 : check start1043 proof1043 = true := by
  decide +kernel

theorem ok1044 : andB (check start1044 proof1044) (cpOk (replay start1044 proof1044) start1045) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
