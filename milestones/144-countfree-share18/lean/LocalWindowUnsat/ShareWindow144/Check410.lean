import LocalWindowUnsat.ShareWindow144.Data410
import LocalWindowUnsat.ShareWindow144.Data411

/-! Kernel checks of segments 1637-1640 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1637 : check start1637 proof1637 = true := by
  decide +kernel

theorem ok1638 : check start1638 proof1638 = true := by
  decide +kernel

theorem ok1639 : check start1639 proof1639 = true := by
  decide +kernel

theorem ok1640 : andB (check start1640 proof1640) (cpOk (replay start1640 proof1640) start1641) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
