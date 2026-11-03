import LocalWindowUnsat.ShareWindow144.Data493
import LocalWindowUnsat.ShareWindow144.Data494

/-! Kernel checks of segments 1969-1972 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1969 : check start1969 proof1969 = true := by
  decide +kernel

theorem ok1970 : check start1970 proof1970 = true := by
  decide +kernel

theorem ok1971 : check start1971 proof1971 = true := by
  decide +kernel

theorem ok1972 : andB (check start1972 proof1972) (cpOk (replay start1972 proof1972) start1973) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
