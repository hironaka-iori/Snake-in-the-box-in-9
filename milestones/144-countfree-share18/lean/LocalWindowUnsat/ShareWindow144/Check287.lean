import LocalWindowUnsat.ShareWindow144.Data287
import LocalWindowUnsat.ShareWindow144.Data288

/-! Kernel checks of segments 1145-1148 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1145 : check start1145 proof1145 = true := by
  decide +kernel

theorem ok1146 : check start1146 proof1146 = true := by
  decide +kernel

theorem ok1147 : check start1147 proof1147 = true := by
  decide +kernel

theorem ok1148 : andB (check start1148 proof1148) (cpOk (replay start1148 proof1148) start1149) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
