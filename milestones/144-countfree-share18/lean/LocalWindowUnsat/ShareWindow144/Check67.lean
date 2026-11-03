import LocalWindowUnsat.ShareWindow144.Data67
import LocalWindowUnsat.ShareWindow144.Data68

/-! Kernel checks of segments 265-268 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok265 : check start265 proof265 = true := by
  decide +kernel

theorem ok266 : check start266 proof266 = true := by
  decide +kernel

theorem ok267 : check start267 proof267 = true := by
  decide +kernel

theorem ok268 : andB (check start268 proof268) (cpOk (replay start268 proof268) start269) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
