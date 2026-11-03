import LocalWindowUnsat.ShareWindow144.Data280
import LocalWindowUnsat.ShareWindow144.Data281

/-! Kernel checks of segments 1117-1120 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1117 : check start1117 proof1117 = true := by
  decide +kernel

theorem ok1118 : check start1118 proof1118 = true := by
  decide +kernel

theorem ok1119 : check start1119 proof1119 = true := by
  decide +kernel

theorem ok1120 : andB (check start1120 proof1120) (cpOk (replay start1120 proof1120) start1121) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
