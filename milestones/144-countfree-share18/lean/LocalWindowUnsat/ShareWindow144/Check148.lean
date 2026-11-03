import LocalWindowUnsat.ShareWindow144.Data148
import LocalWindowUnsat.ShareWindow144.Data149

/-! Kernel checks of segments 589-592 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok589 : check start589 proof589 = true := by
  decide +kernel

theorem ok590 : check start590 proof590 = true := by
  decide +kernel

theorem ok591 : check start591 proof591 = true := by
  decide +kernel

theorem ok592 : andB (check start592 proof592) (cpOk (replay start592 proof592) start593) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
