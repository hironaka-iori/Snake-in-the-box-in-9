import LocalWindowUnsat.ShareWindow144.Data514
import LocalWindowUnsat.ShareWindow144.Data515

/-! Kernel checks of segments 2053-2056 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2053 : check start2053 proof2053 = true := by
  decide +kernel

theorem ok2054 : check start2054 proof2054 = true := by
  decide +kernel

theorem ok2055 : check start2055 proof2055 = true := by
  decide +kernel

theorem ok2056 : andB (check start2056 proof2056) (cpOk (replay start2056 proof2056) start2057) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
