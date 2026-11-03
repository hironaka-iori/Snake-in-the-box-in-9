import LocalWindowUnsat.ShareWindow144.Data476
import LocalWindowUnsat.ShareWindow144.Data477

/-! Kernel checks of segments 1901-1904 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1901 : check start1901 proof1901 = true := by
  decide +kernel

theorem ok1902 : check start1902 proof1902 = true := by
  decide +kernel

theorem ok1903 : check start1903 proof1903 = true := by
  decide +kernel

theorem ok1904 : andB (check start1904 proof1904) (cpOk (replay start1904 proof1904) start1905) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
