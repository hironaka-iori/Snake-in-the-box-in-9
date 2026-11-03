import LocalWindowUnsat.ShareWindow144.Data583
import LocalWindowUnsat.ShareWindow144.Data584

/-! Kernel checks of segments 2329-2332 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2329 : check start2329 proof2329 = true := by
  decide +kernel

theorem ok2330 : check start2330 proof2330 = true := by
  decide +kernel

theorem ok2331 : check start2331 proof2331 = true := by
  decide +kernel

theorem ok2332 : andB (check start2332 proof2332) (cpOk (replay start2332 proof2332) start2333) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
