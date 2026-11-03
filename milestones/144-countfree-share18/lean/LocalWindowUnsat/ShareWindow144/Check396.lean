import LocalWindowUnsat.ShareWindow144.Data396
import LocalWindowUnsat.ShareWindow144.Data397

/-! Kernel checks of segments 1581-1584 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1581 : check start1581 proof1581 = true := by
  decide +kernel

theorem ok1582 : check start1582 proof1582 = true := by
  decide +kernel

theorem ok1583 : check start1583 proof1583 = true := by
  decide +kernel

theorem ok1584 : andB (check start1584 proof1584) (cpOk (replay start1584 proof1584) start1585) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
