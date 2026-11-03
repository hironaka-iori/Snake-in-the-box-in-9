import LocalWindowUnsat.ShareWindow144.Data256
import LocalWindowUnsat.ShareWindow144.Data257

/-! Kernel checks of segments 1021-1024 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1021 : check start1021 proof1021 = true := by
  decide +kernel

theorem ok1022 : check start1022 proof1022 = true := by
  decide +kernel

theorem ok1023 : check start1023 proof1023 = true := by
  decide +kernel

theorem ok1024 : andB (check start1024 proof1024) (cpOk (replay start1024 proof1024) start1025) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
