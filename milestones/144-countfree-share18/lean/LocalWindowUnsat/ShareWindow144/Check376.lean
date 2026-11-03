import LocalWindowUnsat.ShareWindow144.Data376
import LocalWindowUnsat.ShareWindow144.Data377

/-! Kernel checks of segments 1501-1504 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1501 : check start1501 proof1501 = true := by
  decide +kernel

theorem ok1502 : check start1502 proof1502 = true := by
  decide +kernel

theorem ok1503 : check start1503 proof1503 = true := by
  decide +kernel

theorem ok1504 : andB (check start1504 proof1504) (cpOk (replay start1504 proof1504) start1505) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
