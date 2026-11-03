import LocalWindowUnsat.ShareWindow144.Data481
import LocalWindowUnsat.ShareWindow144.Data482

/-! Kernel checks of segments 1921-1924 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1921 : check start1921 proof1921 = true := by
  decide +kernel

theorem ok1922 : check start1922 proof1922 = true := by
  decide +kernel

theorem ok1923 : check start1923 proof1923 = true := by
  decide +kernel

theorem ok1924 : andB (check start1924 proof1924) (cpOk (replay start1924 proof1924) start1925) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
