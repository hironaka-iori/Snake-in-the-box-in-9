import LocalWindowUnsat.ShareWindow144.Data411
import LocalWindowUnsat.ShareWindow144.Data412

/-! Kernel checks of segments 1641-1644 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1641 : check start1641 proof1641 = true := by
  decide +kernel

theorem ok1642 : check start1642 proof1642 = true := by
  decide +kernel

theorem ok1643 : check start1643 proof1643 = true := by
  decide +kernel

theorem ok1644 : andB (check start1644 proof1644) (cpOk (replay start1644 proof1644) start1645) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
