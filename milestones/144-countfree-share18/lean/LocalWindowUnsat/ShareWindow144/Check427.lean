import LocalWindowUnsat.ShareWindow144.Data427
import LocalWindowUnsat.ShareWindow144.Data428

/-! Kernel checks of segments 1705-1708 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1705 : check start1705 proof1705 = true := by
  decide +kernel

theorem ok1706 : check start1706 proof1706 = true := by
  decide +kernel

theorem ok1707 : check start1707 proof1707 = true := by
  decide +kernel

theorem ok1708 : andB (check start1708 proof1708) (cpOk (replay start1708 proof1708) start1709) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
