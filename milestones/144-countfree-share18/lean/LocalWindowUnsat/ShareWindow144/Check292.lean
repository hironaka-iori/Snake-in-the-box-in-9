import LocalWindowUnsat.ShareWindow144.Data292
import LocalWindowUnsat.ShareWindow144.Data293

/-! Kernel checks of segments 1165-1168 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1165 : check start1165 proof1165 = true := by
  decide +kernel

theorem ok1166 : check start1166 proof1166 = true := by
  decide +kernel

theorem ok1167 : check start1167 proof1167 = true := by
  decide +kernel

theorem ok1168 : andB (check start1168 proof1168) (cpOk (replay start1168 proof1168) start1169) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
