import LocalWindowUnsat.ShareWindow144.Data264
import LocalWindowUnsat.ShareWindow144.Data265

/-! Kernel checks of segments 1053-1056 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1053 : check start1053 proof1053 = true := by
  decide +kernel

theorem ok1054 : check start1054 proof1054 = true := by
  decide +kernel

theorem ok1055 : check start1055 proof1055 = true := by
  decide +kernel

theorem ok1056 : andB (check start1056 proof1056) (cpOk (replay start1056 proof1056) start1057) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
