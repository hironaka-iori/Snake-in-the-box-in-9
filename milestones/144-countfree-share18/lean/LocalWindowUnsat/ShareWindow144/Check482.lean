import LocalWindowUnsat.ShareWindow144.Data482
import LocalWindowUnsat.ShareWindow144.Data483

/-! Kernel checks of segments 1925-1928 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1925 : check start1925 proof1925 = true := by
  decide +kernel

theorem ok1926 : check start1926 proof1926 = true := by
  decide +kernel

theorem ok1927 : check start1927 proof1927 = true := by
  decide +kernel

theorem ok1928 : andB (check start1928 proof1928) (cpOk (replay start1928 proof1928) start1929) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
