import LocalWindowUnsat.ShareWindow144.Data282
import LocalWindowUnsat.ShareWindow144.Data283

/-! Kernel checks of segments 1125-1128 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1125 : check start1125 proof1125 = true := by
  decide +kernel

theorem ok1126 : check start1126 proof1126 = true := by
  decide +kernel

theorem ok1127 : check start1127 proof1127 = true := by
  decide +kernel

theorem ok1128 : andB (check start1128 proof1128) (cpOk (replay start1128 proof1128) start1129) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
