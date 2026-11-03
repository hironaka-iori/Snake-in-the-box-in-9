import LocalWindowUnsat.ShareWindow144.Data463
import LocalWindowUnsat.ShareWindow144.Data464

/-! Kernel checks of segments 1849-1852 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1849 : check start1849 proof1849 = true := by
  decide +kernel

theorem ok1850 : check start1850 proof1850 = true := by
  decide +kernel

theorem ok1851 : check start1851 proof1851 = true := by
  decide +kernel

theorem ok1852 : andB (check start1852 proof1852) (cpOk (replay start1852 proof1852) start1853) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
