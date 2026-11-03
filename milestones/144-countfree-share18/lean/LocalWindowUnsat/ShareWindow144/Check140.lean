import LocalWindowUnsat.ShareWindow144.Data140
import LocalWindowUnsat.ShareWindow144.Data141

/-! Kernel checks of segments 557-560 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok557 : check start557 proof557 = true := by
  decide +kernel

theorem ok558 : check start558 proof558 = true := by
  decide +kernel

theorem ok559 : check start559 proof559 = true := by
  decide +kernel

theorem ok560 : andB (check start560 proof560) (cpOk (replay start560 proof560) start561) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
