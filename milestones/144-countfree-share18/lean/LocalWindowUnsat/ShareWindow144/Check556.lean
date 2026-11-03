import LocalWindowUnsat.ShareWindow144.Data556
import LocalWindowUnsat.ShareWindow144.Data557

/-! Kernel checks of segments 2221-2224 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2221 : check start2221 proof2221 = true := by
  decide +kernel

theorem ok2222 : check start2222 proof2222 = true := by
  decide +kernel

theorem ok2223 : check start2223 proof2223 = true := by
  decide +kernel

theorem ok2224 : andB (check start2224 proof2224) (cpOk (replay start2224 proof2224) start2225) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
