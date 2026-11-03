import LocalWindowUnsat.ShareWindow144.Data438
import LocalWindowUnsat.ShareWindow144.Data439

/-! Kernel checks of segments 1749-1752 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1749 : check start1749 proof1749 = true := by
  decide +kernel

theorem ok1750 : check start1750 proof1750 = true := by
  decide +kernel

theorem ok1751 : check start1751 proof1751 = true := by
  decide +kernel

theorem ok1752 : andB (check start1752 proof1752) (cpOk (replay start1752 proof1752) start1753) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
