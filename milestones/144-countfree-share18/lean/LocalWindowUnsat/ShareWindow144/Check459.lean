import LocalWindowUnsat.ShareWindow144.Data459
import LocalWindowUnsat.ShareWindow144.Data460

/-! Kernel checks of segments 1833-1836 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1833 : check start1833 proof1833 = true := by
  decide +kernel

theorem ok1834 : check start1834 proof1834 = true := by
  decide +kernel

theorem ok1835 : check start1835 proof1835 = true := by
  decide +kernel

theorem ok1836 : andB (check start1836 proof1836) (cpOk (replay start1836 proof1836) start1837) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
