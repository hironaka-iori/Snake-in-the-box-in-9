import LocalWindowUnsat.ShareWindow144.Data143
import LocalWindowUnsat.ShareWindow144.Data144

/-! Kernel checks of segments 569-572 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok569 : check start569 proof569 = true := by
  decide +kernel

theorem ok570 : check start570 proof570 = true := by
  decide +kernel

theorem ok571 : check start571 proof571 = true := by
  decide +kernel

theorem ok572 : andB (check start572 proof572) (cpOk (replay start572 proof572) start573) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
