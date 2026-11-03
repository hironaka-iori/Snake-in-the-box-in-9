import LocalWindowUnsat.ShareWindow144.Data428
import LocalWindowUnsat.ShareWindow144.Data429

/-! Kernel checks of segments 1709-1712 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1709 : check start1709 proof1709 = true := by
  decide +kernel

theorem ok1710 : check start1710 proof1710 = true := by
  decide +kernel

theorem ok1711 : check start1711 proof1711 = true := by
  decide +kernel

theorem ok1712 : andB (check start1712 proof1712) (cpOk (replay start1712 proof1712) start1713) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
