import LocalWindowUnsat.ShareWindow144.Data314
import LocalWindowUnsat.ShareWindow144.Data315

/-! Kernel checks of segments 1253-1256 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1253 : check start1253 proof1253 = true := by
  decide +kernel

theorem ok1254 : check start1254 proof1254 = true := by
  decide +kernel

theorem ok1255 : check start1255 proof1255 = true := by
  decide +kernel

theorem ok1256 : andB (check start1256 proof1256) (cpOk (replay start1256 proof1256) start1257) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
