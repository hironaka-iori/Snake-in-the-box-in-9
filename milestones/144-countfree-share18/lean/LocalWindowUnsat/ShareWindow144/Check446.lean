import LocalWindowUnsat.ShareWindow144.Data446
import LocalWindowUnsat.ShareWindow144.Data447

/-! Kernel checks of segments 1781-1784 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1781 : check start1781 proof1781 = true := by
  decide +kernel

theorem ok1782 : check start1782 proof1782 = true := by
  decide +kernel

theorem ok1783 : check start1783 proof1783 = true := by
  decide +kernel

theorem ok1784 : andB (check start1784 proof1784) (cpOk (replay start1784 proof1784) start1785) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
