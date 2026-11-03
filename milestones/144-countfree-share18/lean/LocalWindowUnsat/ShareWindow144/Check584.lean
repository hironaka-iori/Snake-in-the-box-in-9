import LocalWindowUnsat.ShareWindow144.Data584
import LocalWindowUnsat.ShareWindow144.Data585

/-! Kernel checks of segments 2333-2336 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2333 : check start2333 proof2333 = true := by
  decide +kernel

theorem ok2334 : check start2334 proof2334 = true := by
  decide +kernel

theorem ok2335 : check start2335 proof2335 = true := by
  decide +kernel

theorem ok2336 : andB (check start2336 proof2336) (cpOk (replay start2336 proof2336) start2337) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
