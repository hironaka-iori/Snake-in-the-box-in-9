import LocalWindowUnsat.ShareWindow144.Data312
import LocalWindowUnsat.ShareWindow144.Data313

/-! Kernel checks of segments 1245-1248 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1245 : check start1245 proof1245 = true := by
  decide +kernel

theorem ok1246 : check start1246 proof1246 = true := by
  decide +kernel

theorem ok1247 : check start1247 proof1247 = true := by
  decide +kernel

theorem ok1248 : andB (check start1248 proof1248) (cpOk (replay start1248 proof1248) start1249) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
