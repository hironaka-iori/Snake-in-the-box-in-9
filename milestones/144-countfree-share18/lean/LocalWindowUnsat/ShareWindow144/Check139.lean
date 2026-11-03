import LocalWindowUnsat.ShareWindow144.Data139
import LocalWindowUnsat.ShareWindow144.Data140

/-! Kernel checks of segments 553-556 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok553 : check start553 proof553 = true := by
  decide +kernel

theorem ok554 : check start554 proof554 = true := by
  decide +kernel

theorem ok555 : check start555 proof555 = true := by
  decide +kernel

theorem ok556 : andB (check start556 proof556) (cpOk (replay start556 proof556) start557) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
