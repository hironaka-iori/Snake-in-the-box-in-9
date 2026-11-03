import LocalWindowUnsat.ShareWindow144.Data565
import LocalWindowUnsat.ShareWindow144.Data566

/-! Kernel checks of segments 2257-2260 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2257 : check start2257 proof2257 = true := by
  decide +kernel

theorem ok2258 : check start2258 proof2258 = true := by
  decide +kernel

theorem ok2259 : check start2259 proof2259 = true := by
  decide +kernel

theorem ok2260 : andB (check start2260 proof2260) (cpOk (replay start2260 proof2260) start2261) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
