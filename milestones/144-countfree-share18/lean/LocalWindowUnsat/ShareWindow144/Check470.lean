import LocalWindowUnsat.ShareWindow144.Data470
import LocalWindowUnsat.ShareWindow144.Data471

/-! Kernel checks of segments 1877-1880 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1877 : check start1877 proof1877 = true := by
  decide +kernel

theorem ok1878 : check start1878 proof1878 = true := by
  decide +kernel

theorem ok1879 : check start1879 proof1879 = true := by
  decide +kernel

theorem ok1880 : andB (check start1880 proof1880) (cpOk (replay start1880 proof1880) start1881) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
