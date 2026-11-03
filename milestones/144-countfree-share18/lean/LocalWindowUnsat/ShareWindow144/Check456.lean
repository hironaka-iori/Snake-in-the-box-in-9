import LocalWindowUnsat.ShareWindow144.Data456
import LocalWindowUnsat.ShareWindow144.Data457

/-! Kernel checks of segments 1821-1824 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1821 : check start1821 proof1821 = true := by
  decide +kernel

theorem ok1822 : check start1822 proof1822 = true := by
  decide +kernel

theorem ok1823 : check start1823 proof1823 = true := by
  decide +kernel

theorem ok1824 : andB (check start1824 proof1824) (cpOk (replay start1824 proof1824) start1825) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
