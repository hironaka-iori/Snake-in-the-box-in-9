import LocalWindowUnsat.ShareWindow144.Data274
import LocalWindowUnsat.ShareWindow144.Data275

/-! Kernel checks of segments 1093-1096 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1093 : check start1093 proof1093 = true := by
  decide +kernel

theorem ok1094 : check start1094 proof1094 = true := by
  decide +kernel

theorem ok1095 : check start1095 proof1095 = true := by
  decide +kernel

theorem ok1096 : andB (check start1096 proof1096) (cpOk (replay start1096 proof1096) start1097) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
