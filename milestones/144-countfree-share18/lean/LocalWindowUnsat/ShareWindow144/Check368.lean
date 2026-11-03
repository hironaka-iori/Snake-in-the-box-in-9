import LocalWindowUnsat.ShareWindow144.Data368
import LocalWindowUnsat.ShareWindow144.Data369

/-! Kernel checks of segments 1469-1472 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1469 : check start1469 proof1469 = true := by
  decide +kernel

theorem ok1470 : check start1470 proof1470 = true := by
  decide +kernel

theorem ok1471 : check start1471 proof1471 = true := by
  decide +kernel

theorem ok1472 : andB (check start1472 proof1472) (cpOk (replay start1472 proof1472) start1473) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
