import LocalWindowUnsat.ShareWindow144.Data304
import LocalWindowUnsat.ShareWindow144.Data305

/-! Kernel checks of segments 1213-1216 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1213 : check start1213 proof1213 = true := by
  decide +kernel

theorem ok1214 : check start1214 proof1214 = true := by
  decide +kernel

theorem ok1215 : check start1215 proof1215 = true := by
  decide +kernel

theorem ok1216 : andB (check start1216 proof1216) (cpOk (replay start1216 proof1216) start1217) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
