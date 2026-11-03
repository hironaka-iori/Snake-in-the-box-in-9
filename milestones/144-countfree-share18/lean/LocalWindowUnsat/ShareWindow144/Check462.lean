import LocalWindowUnsat.ShareWindow144.Data462
import LocalWindowUnsat.ShareWindow144.Data463

/-! Kernel checks of segments 1845-1848 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1845 : check start1845 proof1845 = true := by
  decide +kernel

theorem ok1846 : check start1846 proof1846 = true := by
  decide +kernel

theorem ok1847 : check start1847 proof1847 = true := by
  decide +kernel

theorem ok1848 : andB (check start1848 proof1848) (cpOk (replay start1848 proof1848) start1849) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
