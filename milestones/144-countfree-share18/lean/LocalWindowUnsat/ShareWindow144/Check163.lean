import LocalWindowUnsat.ShareWindow144.Data163
import LocalWindowUnsat.ShareWindow144.Data164

/-! Kernel checks of segments 649-652 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok649 : check start649 proof649 = true := by
  decide +kernel

theorem ok650 : check start650 proof650 = true := by
  decide +kernel

theorem ok651 : check start651 proof651 = true := by
  decide +kernel

theorem ok652 : andB (check start652 proof652) (cpOk (replay start652 proof652) start653) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
