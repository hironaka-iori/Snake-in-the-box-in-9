import LocalWindowUnsat.ShareWindow144.Data297
import LocalWindowUnsat.ShareWindow144.Data298

/-! Kernel checks of segments 1185-1188 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1185 : check start1185 proof1185 = true := by
  decide +kernel

theorem ok1186 : check start1186 proof1186 = true := by
  decide +kernel

theorem ok1187 : check start1187 proof1187 = true := by
  decide +kernel

theorem ok1188 : andB (check start1188 proof1188) (cpOk (replay start1188 proof1188) start1189) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
