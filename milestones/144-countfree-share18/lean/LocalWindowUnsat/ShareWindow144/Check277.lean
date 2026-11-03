import LocalWindowUnsat.ShareWindow144.Data277
import LocalWindowUnsat.ShareWindow144.Data278

/-! Kernel checks of segments 1105-1108 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1105 : check start1105 proof1105 = true := by
  decide +kernel

theorem ok1106 : check start1106 proof1106 = true := by
  decide +kernel

theorem ok1107 : check start1107 proof1107 = true := by
  decide +kernel

theorem ok1108 : andB (check start1108 proof1108) (cpOk (replay start1108 proof1108) start1109) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
