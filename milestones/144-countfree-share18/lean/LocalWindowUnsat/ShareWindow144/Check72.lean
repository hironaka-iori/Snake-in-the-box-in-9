import LocalWindowUnsat.ShareWindow144.Data72
import LocalWindowUnsat.ShareWindow144.Data73

/-! Kernel checks of segments 285-288 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok285 : check start285 proof285 = true := by
  decide +kernel

theorem ok286 : check start286 proof286 = true := by
  decide +kernel

theorem ok287 : check start287 proof287 = true := by
  decide +kernel

theorem ok288 : andB (check start288 proof288) (cpOk (replay start288 proof288) start289) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
