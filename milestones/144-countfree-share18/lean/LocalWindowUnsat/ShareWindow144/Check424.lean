import LocalWindowUnsat.ShareWindow144.Data424
import LocalWindowUnsat.ShareWindow144.Data425

/-! Kernel checks of segments 1693-1696 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1693 : check start1693 proof1693 = true := by
  decide +kernel

theorem ok1694 : check start1694 proof1694 = true := by
  decide +kernel

theorem ok1695 : check start1695 proof1695 = true := by
  decide +kernel

theorem ok1696 : andB (check start1696 proof1696) (cpOk (replay start1696 proof1696) start1697) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
