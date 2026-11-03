import LocalWindowUnsat.ShareWindow144.Data451
import LocalWindowUnsat.ShareWindow144.Data452

/-! Kernel checks of segments 1801-1804 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1801 : check start1801 proof1801 = true := by
  decide +kernel

theorem ok1802 : check start1802 proof1802 = true := by
  decide +kernel

theorem ok1803 : check start1803 proof1803 = true := by
  decide +kernel

theorem ok1804 : andB (check start1804 proof1804) (cpOk (replay start1804 proof1804) start1805) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
