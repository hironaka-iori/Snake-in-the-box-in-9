import LocalWindowUnsat.ShareWindow144.Data220
import LocalWindowUnsat.ShareWindow144.Data221

/-! Kernel checks of segments 877-880 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok877 : check start877 proof877 = true := by
  decide +kernel

theorem ok878 : check start878 proof878 = true := by
  decide +kernel

theorem ok879 : check start879 proof879 = true := by
  decide +kernel

theorem ok880 : andB (check start880 proof880) (cpOk (replay start880 proof880) start881) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
