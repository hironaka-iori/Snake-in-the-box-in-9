import LocalWindowUnsat.ShareWindow144.Data526
import LocalWindowUnsat.ShareWindow144.Data527

/-! Kernel checks of segments 2101-2104 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2101 : check start2101 proof2101 = true := by
  decide +kernel

theorem ok2102 : check start2102 proof2102 = true := by
  decide +kernel

theorem ok2103 : check start2103 proof2103 = true := by
  decide +kernel

theorem ok2104 : andB (check start2104 proof2104) (cpOk (replay start2104 proof2104) start2105) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
