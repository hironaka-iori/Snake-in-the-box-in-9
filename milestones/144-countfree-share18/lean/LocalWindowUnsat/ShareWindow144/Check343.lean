import LocalWindowUnsat.ShareWindow144.Data343
import LocalWindowUnsat.ShareWindow144.Data344

/-! Kernel checks of segments 1369-1372 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1369 : check start1369 proof1369 = true := by
  decide +kernel

theorem ok1370 : check start1370 proof1370 = true := by
  decide +kernel

theorem ok1371 : check start1371 proof1371 = true := by
  decide +kernel

theorem ok1372 : andB (check start1372 proof1372) (cpOk (replay start1372 proof1372) start1373) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
