import LocalWindowUnsat.ShareWindow144.Data310
import LocalWindowUnsat.ShareWindow144.Data311

/-! Kernel checks of segments 1237-1240 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1237 : check start1237 proof1237 = true := by
  decide +kernel

theorem ok1238 : check start1238 proof1238 = true := by
  decide +kernel

theorem ok1239 : check start1239 proof1239 = true := by
  decide +kernel

theorem ok1240 : andB (check start1240 proof1240) (cpOk (replay start1240 proof1240) start1241) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
