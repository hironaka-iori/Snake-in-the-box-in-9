import LocalWindowUnsat.ShareWindow144.Data464
import LocalWindowUnsat.ShareWindow144.Data465

/-! Kernel checks of segments 1853-1856 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1853 : check start1853 proof1853 = true := by
  decide +kernel

theorem ok1854 : check start1854 proof1854 = true := by
  decide +kernel

theorem ok1855 : check start1855 proof1855 = true := by
  decide +kernel

theorem ok1856 : andB (check start1856 proof1856) (cpOk (replay start1856 proof1856) start1857) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
