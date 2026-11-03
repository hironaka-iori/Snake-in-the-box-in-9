import LocalWindowUnsat.ShareWindow144.Data437
import LocalWindowUnsat.ShareWindow144.Data438

/-! Kernel checks of segments 1745-1748 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1745 : check start1745 proof1745 = true := by
  decide +kernel

theorem ok1746 : check start1746 proof1746 = true := by
  decide +kernel

theorem ok1747 : check start1747 proof1747 = true := by
  decide +kernel

theorem ok1748 : andB (check start1748 proof1748) (cpOk (replay start1748 proof1748) start1749) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
