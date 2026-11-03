import LocalWindowUnsat.ShareWindow144.Data16
import LocalWindowUnsat.ShareWindow144.Data17

/-! Kernel checks of segments 61-64 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok61 : check start61 proof61 = true := by
  decide +kernel

theorem ok62 : check start62 proof62 = true := by
  decide +kernel

theorem ok63 : check start63 proof63 = true := by
  decide +kernel

theorem ok64 : andB (check start64 proof64) (cpOk (replay start64 proof64) start65) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
