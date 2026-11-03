import LocalWindowUnsat.ShareWindow144.Data564
import LocalWindowUnsat.ShareWindow144.Data565

/-! Kernel checks of segments 2253-2256 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2253 : check start2253 proof2253 = true := by
  decide +kernel

theorem ok2254 : check start2254 proof2254 = true := by
  decide +kernel

theorem ok2255 : check start2255 proof2255 = true := by
  decide +kernel

theorem ok2256 : andB (check start2256 proof2256) (cpOk (replay start2256 proof2256) start2257) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
