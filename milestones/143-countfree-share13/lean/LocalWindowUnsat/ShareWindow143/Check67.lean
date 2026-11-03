import LocalWindowUnsat.ShareWindow143.Data67
import LocalWindowUnsat.ShareWindow143.Data68

/-! Kernel checks of segments 265-268 of `share143` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow143
open Snake9.LratFast143
open Snake9.Lrat143 (Tree TreeTrue andB)

theorem ok265 : check start265 proof265 = true := by
  decide +kernel

theorem ok266 : check start266 proof266 = true := by
  decide +kernel

theorem ok267 : check start267 proof267 = true := by
  decide +kernel

theorem ok268 : andB (check start268 proof268) (cpOk (replay start268 proof268) start269) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow143
