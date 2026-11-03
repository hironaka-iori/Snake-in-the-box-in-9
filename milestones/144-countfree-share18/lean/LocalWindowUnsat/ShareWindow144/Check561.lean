import LocalWindowUnsat.ShareWindow144.Data561
import LocalWindowUnsat.ShareWindow144.Data562

/-! Kernel checks of segments 2241-2244 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2241 : check start2241 proof2241 = true := by
  decide +kernel

theorem ok2242 : check start2242 proof2242 = true := by
  decide +kernel

theorem ok2243 : check start2243 proof2243 = true := by
  decide +kernel

theorem ok2244 : andB (check start2244 proof2244) (cpOk (replay start2244 proof2244) start2245) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
