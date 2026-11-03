import LocalWindowUnsat.ShareWindow144.Data326
import LocalWindowUnsat.ShareWindow144.Data327

/-! Kernel checks of segments 1301-1304 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1301 : check start1301 proof1301 = true := by
  decide +kernel

theorem ok1302 : check start1302 proof1302 = true := by
  decide +kernel

theorem ok1303 : check start1303 proof1303 = true := by
  decide +kernel

theorem ok1304 : andB (check start1304 proof1304) (cpOk (replay start1304 proof1304) start1305) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
