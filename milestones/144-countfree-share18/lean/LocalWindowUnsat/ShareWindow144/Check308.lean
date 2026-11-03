import LocalWindowUnsat.ShareWindow144.Data308
import LocalWindowUnsat.ShareWindow144.Data309

/-! Kernel checks of segments 1229-1232 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1229 : check start1229 proof1229 = true := by
  decide +kernel

theorem ok1230 : check start1230 proof1230 = true := by
  decide +kernel

theorem ok1231 : check start1231 proof1231 = true := by
  decide +kernel

theorem ok1232 : andB (check start1232 proof1232) (cpOk (replay start1232 proof1232) start1233) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
