import LocalWindowUnsat.ShareWindow144.Data267
import LocalWindowUnsat.ShareWindow144.Data268

/-! Kernel checks of segments 1065-1068 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1065 : check start1065 proof1065 = true := by
  decide +kernel

theorem ok1066 : check start1066 proof1066 = true := by
  decide +kernel

theorem ok1067 : check start1067 proof1067 = true := by
  decide +kernel

theorem ok1068 : andB (check start1068 proof1068) (cpOk (replay start1068 proof1068) start1069) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
