import LocalWindowUnsat.ShareWindow144.Data167
import LocalWindowUnsat.ShareWindow144.Data168

/-! Kernel checks of segments 665-668 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok665 : check start665 proof665 = true := by
  decide +kernel

theorem ok666 : check start666 proof666 = true := by
  decide +kernel

theorem ok667 : check start667 proof667 = true := by
  decide +kernel

theorem ok668 : andB (check start668 proof668) (cpOk (replay start668 proof668) start669) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
