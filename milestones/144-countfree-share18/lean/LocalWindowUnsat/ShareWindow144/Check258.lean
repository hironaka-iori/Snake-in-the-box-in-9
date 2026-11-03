import LocalWindowUnsat.ShareWindow144.Data258
import LocalWindowUnsat.ShareWindow144.Data259

/-! Kernel checks of segments 1029-1032 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1029 : check start1029 proof1029 = true := by
  decide +kernel

theorem ok1030 : check start1030 proof1030 = true := by
  decide +kernel

theorem ok1031 : check start1031 proof1031 = true := by
  decide +kernel

theorem ok1032 : andB (check start1032 proof1032) (cpOk (replay start1032 proof1032) start1033) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
