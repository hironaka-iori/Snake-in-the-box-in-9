import LocalWindowUnsat.ShareWindow144.Data118
import LocalWindowUnsat.ShareWindow144.Data119

/-! Kernel checks of segments 469-472 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok469 : check start469 proof469 = true := by
  decide +kernel

theorem ok470 : check start470 proof470 = true := by
  decide +kernel

theorem ok471 : check start471 proof471 = true := by
  decide +kernel

theorem ok472 : andB (check start472 proof472) (cpOk (replay start472 proof472) start473) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
