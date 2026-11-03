import LocalWindowUnsat.ShareWindow144.Data260
import LocalWindowUnsat.ShareWindow144.Data261

/-! Kernel checks of segments 1037-1040 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1037 : check start1037 proof1037 = true := by
  decide +kernel

theorem ok1038 : check start1038 proof1038 = true := by
  decide +kernel

theorem ok1039 : check start1039 proof1039 = true := by
  decide +kernel

theorem ok1040 : andB (check start1040 proof1040) (cpOk (replay start1040 proof1040) start1041) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
