import LocalWindowUnsat.ShareWindow144.Data400
import LocalWindowUnsat.ShareWindow144.Data401

/-! Kernel checks of segments 1597-1600 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1597 : check start1597 proof1597 = true := by
  decide +kernel

theorem ok1598 : check start1598 proof1598 = true := by
  decide +kernel

theorem ok1599 : check start1599 proof1599 = true := by
  decide +kernel

theorem ok1600 : andB (check start1600 proof1600) (cpOk (replay start1600 proof1600) start1601) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
