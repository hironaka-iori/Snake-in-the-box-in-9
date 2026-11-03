import LocalWindowUnsat.ShareWindow144.Data240
import LocalWindowUnsat.ShareWindow144.Data241

/-! Kernel checks of segments 957-960 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok957 : check start957 proof957 = true := by
  decide +kernel

theorem ok958 : check start958 proof958 = true := by
  decide +kernel

theorem ok959 : check start959 proof959 = true := by
  decide +kernel

theorem ok960 : andB (check start960 proof960) (cpOk (replay start960 proof960) start961) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
