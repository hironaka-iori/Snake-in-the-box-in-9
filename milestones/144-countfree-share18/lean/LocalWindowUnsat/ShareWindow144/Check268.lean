import LocalWindowUnsat.ShareWindow144.Data268
import LocalWindowUnsat.ShareWindow144.Data269

/-! Kernel checks of segments 1069-1072 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1069 : check start1069 proof1069 = true := by
  decide +kernel

theorem ok1070 : check start1070 proof1070 = true := by
  decide +kernel

theorem ok1071 : check start1071 proof1071 = true := by
  decide +kernel

theorem ok1072 : andB (check start1072 proof1072) (cpOk (replay start1072 proof1072) start1073) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
