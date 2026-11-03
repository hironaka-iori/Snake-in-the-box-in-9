import LocalWindowUnsat.ShareWindow144.Data276
import LocalWindowUnsat.ShareWindow144.Data277

/-! Kernel checks of segments 1101-1104 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1101 : check start1101 proof1101 = true := by
  decide +kernel

theorem ok1102 : check start1102 proof1102 = true := by
  decide +kernel

theorem ok1103 : check start1103 proof1103 = true := by
  decide +kernel

theorem ok1104 : andB (check start1104 proof1104) (cpOk (replay start1104 proof1104) start1105) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
