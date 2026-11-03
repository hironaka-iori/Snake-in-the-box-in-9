import LocalWindowUnsat.ShareWindow144.Data495
import LocalWindowUnsat.ShareWindow144.Data496

/-! Kernel checks of segments 1977-1980 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1977 : check start1977 proof1977 = true := by
  decide +kernel

theorem ok1978 : check start1978 proof1978 = true := by
  decide +kernel

theorem ok1979 : check start1979 proof1979 = true := by
  decide +kernel

theorem ok1980 : andB (check start1980 proof1980) (cpOk (replay start1980 proof1980) start1981) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
