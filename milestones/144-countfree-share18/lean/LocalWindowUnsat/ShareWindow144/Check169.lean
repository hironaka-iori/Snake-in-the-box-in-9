import LocalWindowUnsat.ShareWindow144.Data169
import LocalWindowUnsat.ShareWindow144.Data170

/-! Kernel checks of segments 673-676 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok673 : check start673 proof673 = true := by
  decide +kernel

theorem ok674 : check start674 proof674 = true := by
  decide +kernel

theorem ok675 : check start675 proof675 = true := by
  decide +kernel

theorem ok676 : andB (check start676 proof676) (cpOk (replay start676 proof676) start677) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
