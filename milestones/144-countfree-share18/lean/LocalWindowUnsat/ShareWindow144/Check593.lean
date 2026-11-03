import LocalWindowUnsat.ShareWindow144.Data593
import LocalWindowUnsat.ShareWindow144.Data594

/-! Kernel checks of segments 2369-2372 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2369 : check start2369 proof2369 = true := by
  decide +kernel

theorem ok2370 : check start2370 proof2370 = true := by
  decide +kernel

theorem ok2371 : check start2371 proof2371 = true := by
  decide +kernel

theorem ok2372 : andB (check start2372 proof2372) (cpOk (replay start2372 proof2372) start2373) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
