import LocalWindowUnsat.ShareWindow144.Data545
import LocalWindowUnsat.ShareWindow144.Data546

/-! Kernel checks of segments 2177-2180 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2177 : check start2177 proof2177 = true := by
  decide +kernel

theorem ok2178 : check start2178 proof2178 = true := by
  decide +kernel

theorem ok2179 : check start2179 proof2179 = true := by
  decide +kernel

theorem ok2180 : andB (check start2180 proof2180) (cpOk (replay start2180 proof2180) start2181) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
