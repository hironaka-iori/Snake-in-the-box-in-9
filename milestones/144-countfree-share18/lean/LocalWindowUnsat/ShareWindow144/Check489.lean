import LocalWindowUnsat.ShareWindow144.Data489
import LocalWindowUnsat.ShareWindow144.Data490

/-! Kernel checks of segments 1953-1956 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1953 : check start1953 proof1953 = true := by
  decide +kernel

theorem ok1954 : check start1954 proof1954 = true := by
  decide +kernel

theorem ok1955 : check start1955 proof1955 = true := by
  decide +kernel

theorem ok1956 : andB (check start1956 proof1956) (cpOk (replay start1956 proof1956) start1957) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
