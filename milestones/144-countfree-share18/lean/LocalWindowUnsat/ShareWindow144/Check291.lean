import LocalWindowUnsat.ShareWindow144.Data291
import LocalWindowUnsat.ShareWindow144.Data292

/-! Kernel checks of segments 1161-1164 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1161 : check start1161 proof1161 = true := by
  decide +kernel

theorem ok1162 : check start1162 proof1162 = true := by
  decide +kernel

theorem ok1163 : check start1163 proof1163 = true := by
  decide +kernel

theorem ok1164 : andB (check start1164 proof1164) (cpOk (replay start1164 proof1164) start1165) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
