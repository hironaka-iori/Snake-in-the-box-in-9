import LocalWindowUnsat.ShareWindow144.Data471
import LocalWindowUnsat.ShareWindow144.Data472

/-! Kernel checks of segments 1881-1884 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1881 : check start1881 proof1881 = true := by
  decide +kernel

theorem ok1882 : check start1882 proof1882 = true := by
  decide +kernel

theorem ok1883 : check start1883 proof1883 = true := by
  decide +kernel

theorem ok1884 : andB (check start1884 proof1884) (cpOk (replay start1884 proof1884) start1885) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
