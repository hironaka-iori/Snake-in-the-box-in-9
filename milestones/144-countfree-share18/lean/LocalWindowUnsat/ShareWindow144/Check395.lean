import LocalWindowUnsat.ShareWindow144.Data395
import LocalWindowUnsat.ShareWindow144.Data396

/-! Kernel checks of segments 1577-1580 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1577 : check start1577 proof1577 = true := by
  decide +kernel

theorem ok1578 : check start1578 proof1578 = true := by
  decide +kernel

theorem ok1579 : check start1579 proof1579 = true := by
  decide +kernel

theorem ok1580 : andB (check start1580 proof1580) (cpOk (replay start1580 proof1580) start1581) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
