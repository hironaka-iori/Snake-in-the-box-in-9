import LocalWindowUnsat.ShareWindow144.Data483
import LocalWindowUnsat.ShareWindow144.Data484

/-! Kernel checks of segments 1929-1932 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1929 : check start1929 proof1929 = true := by
  decide +kernel

theorem ok1930 : check start1930 proof1930 = true := by
  decide +kernel

theorem ok1931 : check start1931 proof1931 = true := by
  decide +kernel

theorem ok1932 : andB (check start1932 proof1932) (cpOk (replay start1932 proof1932) start1933) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
