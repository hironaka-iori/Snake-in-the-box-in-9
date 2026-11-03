import LocalWindowUnsat.ShareWindow144.Data315
import LocalWindowUnsat.ShareWindow144.Data316

/-! Kernel checks of segments 1257-1260 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1257 : check start1257 proof1257 = true := by
  decide +kernel

theorem ok1258 : check start1258 proof1258 = true := by
  decide +kernel

theorem ok1259 : check start1259 proof1259 = true := by
  decide +kernel

theorem ok1260 : andB (check start1260 proof1260) (cpOk (replay start1260 proof1260) start1261) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
