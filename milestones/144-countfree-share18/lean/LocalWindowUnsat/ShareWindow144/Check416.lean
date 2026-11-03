import LocalWindowUnsat.ShareWindow144.Data416
import LocalWindowUnsat.ShareWindow144.Data417

/-! Kernel checks of segments 1661-1664 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1661 : check start1661 proof1661 = true := by
  decide +kernel

theorem ok1662 : check start1662 proof1662 = true := by
  decide +kernel

theorem ok1663 : check start1663 proof1663 = true := by
  decide +kernel

theorem ok1664 : andB (check start1664 proof1664) (cpOk (replay start1664 proof1664) start1665) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
