import LocalWindowUnsat.ShareWindow144.Data279
import LocalWindowUnsat.ShareWindow144.Data280

/-! Kernel checks of segments 1113-1116 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1113 : check start1113 proof1113 = true := by
  decide +kernel

theorem ok1114 : check start1114 proof1114 = true := by
  decide +kernel

theorem ok1115 : check start1115 proof1115 = true := by
  decide +kernel

theorem ok1116 : andB (check start1116 proof1116) (cpOk (replay start1116 proof1116) start1117) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
