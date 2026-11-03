import LocalWindowUnsat.ShareWindow144.Data530
import LocalWindowUnsat.ShareWindow144.Data531

/-! Kernel checks of segments 2117-2120 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2117 : check start2117 proof2117 = true := by
  decide +kernel

theorem ok2118 : check start2118 proof2118 = true := by
  decide +kernel

theorem ok2119 : check start2119 proof2119 = true := by
  decide +kernel

theorem ok2120 : andB (check start2120 proof2120) (cpOk (replay start2120 proof2120) start2121) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
