import LocalWindowUnsat.ShareWindow144.Data461
import LocalWindowUnsat.ShareWindow144.Data462

/-! Kernel checks of segments 1841-1844 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1841 : check start1841 proof1841 = true := by
  decide +kernel

theorem ok1842 : check start1842 proof1842 = true := by
  decide +kernel

theorem ok1843 : check start1843 proof1843 = true := by
  decide +kernel

theorem ok1844 : andB (check start1844 proof1844) (cpOk (replay start1844 proof1844) start1845) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
