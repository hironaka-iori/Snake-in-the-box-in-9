import LocalWindowUnsat.ShareWindow144.Data487
import LocalWindowUnsat.ShareWindow144.Data488

/-! Kernel checks of segments 1945-1948 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1945 : check start1945 proof1945 = true := by
  decide +kernel

theorem ok1946 : check start1946 proof1946 = true := by
  decide +kernel

theorem ok1947 : check start1947 proof1947 = true := by
  decide +kernel

theorem ok1948 : andB (check start1948 proof1948) (cpOk (replay start1948 proof1948) start1949) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
