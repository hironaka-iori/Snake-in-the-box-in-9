import LocalWindowUnsat.ShareWindow144.Data474
import LocalWindowUnsat.ShareWindow144.Data475

/-! Kernel checks of segments 1893-1896 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1893 : check start1893 proof1893 = true := by
  decide +kernel

theorem ok1894 : check start1894 proof1894 = true := by
  decide +kernel

theorem ok1895 : check start1895 proof1895 = true := by
  decide +kernel

theorem ok1896 : andB (check start1896 proof1896) (cpOk (replay start1896 proof1896) start1897) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
