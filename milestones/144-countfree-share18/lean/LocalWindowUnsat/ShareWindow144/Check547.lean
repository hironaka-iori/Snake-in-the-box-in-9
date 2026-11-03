import LocalWindowUnsat.ShareWindow144.Data547
import LocalWindowUnsat.ShareWindow144.Data548

/-! Kernel checks of segments 2185-2188 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2185 : check start2185 proof2185 = true := by
  decide +kernel

theorem ok2186 : check start2186 proof2186 = true := by
  decide +kernel

theorem ok2187 : check start2187 proof2187 = true := by
  decide +kernel

theorem ok2188 : andB (check start2188 proof2188) (cpOk (replay start2188 proof2188) start2189) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
