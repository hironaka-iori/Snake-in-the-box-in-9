import LocalWindowUnsat.ShareWindow144.Data457
import LocalWindowUnsat.ShareWindow144.Data458

/-! Kernel checks of segments 1825-1828 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1825 : check start1825 proof1825 = true := by
  decide +kernel

theorem ok1826 : check start1826 proof1826 = true := by
  decide +kernel

theorem ok1827 : check start1827 proof1827 = true := by
  decide +kernel

theorem ok1828 : andB (check start1828 proof1828) (cpOk (replay start1828 proof1828) start1829) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
