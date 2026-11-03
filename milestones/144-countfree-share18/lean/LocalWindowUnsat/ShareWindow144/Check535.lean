import LocalWindowUnsat.ShareWindow144.Data535
import LocalWindowUnsat.ShareWindow144.Data536

/-! Kernel checks of segments 2137-2140 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2137 : check start2137 proof2137 = true := by
  decide +kernel

theorem ok2138 : check start2138 proof2138 = true := by
  decide +kernel

theorem ok2139 : check start2139 proof2139 = true := by
  decide +kernel

theorem ok2140 : andB (check start2140 proof2140) (cpOk (replay start2140 proof2140) start2141) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
