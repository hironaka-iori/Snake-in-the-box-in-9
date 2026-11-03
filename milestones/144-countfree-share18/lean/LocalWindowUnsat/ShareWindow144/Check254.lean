import LocalWindowUnsat.ShareWindow144.Data254
import LocalWindowUnsat.ShareWindow144.Data255

/-! Kernel checks of segments 1013-1016 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1013 : check start1013 proof1013 = true := by
  decide +kernel

theorem ok1014 : check start1014 proof1014 = true := by
  decide +kernel

theorem ok1015 : check start1015 proof1015 = true := by
  decide +kernel

theorem ok1016 : andB (check start1016 proof1016) (cpOk (replay start1016 proof1016) start1017) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
