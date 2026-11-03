import LocalWindowUnsat.ShareWindow144.Data536
import LocalWindowUnsat.ShareWindow144.Data537

/-! Kernel checks of segments 2141-2144 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2141 : check start2141 proof2141 = true := by
  decide +kernel

theorem ok2142 : check start2142 proof2142 = true := by
  decide +kernel

theorem ok2143 : check start2143 proof2143 = true := by
  decide +kernel

theorem ok2144 : andB (check start2144 proof2144) (cpOk (replay start2144 proof2144) start2145) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
