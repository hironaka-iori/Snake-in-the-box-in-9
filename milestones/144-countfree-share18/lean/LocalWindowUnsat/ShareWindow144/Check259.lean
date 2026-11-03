import LocalWindowUnsat.ShareWindow144.Data259
import LocalWindowUnsat.ShareWindow144.Data260

/-! Kernel checks of segments 1033-1036 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1033 : check start1033 proof1033 = true := by
  decide +kernel

theorem ok1034 : check start1034 proof1034 = true := by
  decide +kernel

theorem ok1035 : check start1035 proof1035 = true := by
  decide +kernel

theorem ok1036 : andB (check start1036 proof1036) (cpOk (replay start1036 proof1036) start1037) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
