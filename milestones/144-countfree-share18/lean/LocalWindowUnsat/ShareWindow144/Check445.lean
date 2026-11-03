import LocalWindowUnsat.ShareWindow144.Data445
import LocalWindowUnsat.ShareWindow144.Data446

/-! Kernel checks of segments 1777-1780 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1777 : check start1777 proof1777 = true := by
  decide +kernel

theorem ok1778 : check start1778 proof1778 = true := by
  decide +kernel

theorem ok1779 : check start1779 proof1779 = true := by
  decide +kernel

theorem ok1780 : andB (check start1780 proof1780) (cpOk (replay start1780 proof1780) start1781) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
