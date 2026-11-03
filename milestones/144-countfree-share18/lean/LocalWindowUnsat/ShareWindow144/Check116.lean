import LocalWindowUnsat.ShareWindow144.Data116
import LocalWindowUnsat.ShareWindow144.Data117

/-! Kernel checks of segments 461-464 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok461 : check start461 proof461 = true := by
  decide +kernel

theorem ok462 : check start462 proof462 = true := by
  decide +kernel

theorem ok463 : check start463 proof463 = true := by
  decide +kernel

theorem ok464 : andB (check start464 proof464) (cpOk (replay start464 proof464) start465) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
