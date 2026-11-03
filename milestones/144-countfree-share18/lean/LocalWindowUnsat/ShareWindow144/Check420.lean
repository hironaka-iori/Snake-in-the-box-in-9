import LocalWindowUnsat.ShareWindow144.Data420
import LocalWindowUnsat.ShareWindow144.Data421

/-! Kernel checks of segments 1677-1680 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1677 : check start1677 proof1677 = true := by
  decide +kernel

theorem ok1678 : check start1678 proof1678 = true := by
  decide +kernel

theorem ok1679 : check start1679 proof1679 = true := by
  decide +kernel

theorem ok1680 : andB (check start1680 proof1680) (cpOk (replay start1680 proof1680) start1681) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
