import LocalWindowUnsat.ShareWindow144.Data494
import LocalWindowUnsat.ShareWindow144.Data495

/-! Kernel checks of segments 1973-1976 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1973 : check start1973 proof1973 = true := by
  decide +kernel

theorem ok1974 : check start1974 proof1974 = true := by
  decide +kernel

theorem ok1975 : check start1975 proof1975 = true := by
  decide +kernel

theorem ok1976 : andB (check start1976 proof1976) (cpOk (replay start1976 proof1976) start1977) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
