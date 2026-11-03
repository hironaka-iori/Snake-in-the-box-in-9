import LocalWindowUnsat.ShareWindow144.Data296
import LocalWindowUnsat.ShareWindow144.Data297

/-! Kernel checks of segments 1181-1184 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1181 : check start1181 proof1181 = true := by
  decide +kernel

theorem ok1182 : check start1182 proof1182 = true := by
  decide +kernel

theorem ok1183 : check start1183 proof1183 = true := by
  decide +kernel

theorem ok1184 : andB (check start1184 proof1184) (cpOk (replay start1184 proof1184) start1185) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
