import LocalWindowUnsat.ShareWindow144.Data293
import LocalWindowUnsat.ShareWindow144.Data294

/-! Kernel checks of segments 1169-1172 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1169 : check start1169 proof1169 = true := by
  decide +kernel

theorem ok1170 : check start1170 proof1170 = true := by
  decide +kernel

theorem ok1171 : check start1171 proof1171 = true := by
  decide +kernel

theorem ok1172 : andB (check start1172 proof1172) (cpOk (replay start1172 proof1172) start1173) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
