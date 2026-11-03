import LocalWindowUnsat.ShareWindow144.Data255
import LocalWindowUnsat.ShareWindow144.Data256

/-! Kernel checks of segments 1017-1020 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1017 : check start1017 proof1017 = true := by
  decide +kernel

theorem ok1018 : check start1018 proof1018 = true := by
  decide +kernel

theorem ok1019 : check start1019 proof1019 = true := by
  decide +kernel

theorem ok1020 : andB (check start1020 proof1020) (cpOk (replay start1020 proof1020) start1021) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
