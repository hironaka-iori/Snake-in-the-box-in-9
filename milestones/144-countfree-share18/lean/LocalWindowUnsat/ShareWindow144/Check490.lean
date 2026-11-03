import LocalWindowUnsat.ShareWindow144.Data490
import LocalWindowUnsat.ShareWindow144.Data491

/-! Kernel checks of segments 1957-1960 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1957 : check start1957 proof1957 = true := by
  decide +kernel

theorem ok1958 : check start1958 proof1958 = true := by
  decide +kernel

theorem ok1959 : check start1959 proof1959 = true := by
  decide +kernel

theorem ok1960 : andB (check start1960 proof1960) (cpOk (replay start1960 proof1960) start1961) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
