import LocalWindowUnsat.ShareWindow144.Data263
import LocalWindowUnsat.ShareWindow144.Data264

/-! Kernel checks of segments 1049-1052 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1049 : check start1049 proof1049 = true := by
  decide +kernel

theorem ok1050 : check start1050 proof1050 = true := by
  decide +kernel

theorem ok1051 : check start1051 proof1051 = true := by
  decide +kernel

theorem ok1052 : andB (check start1052 proof1052) (cpOk (replay start1052 proof1052) start1053) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
