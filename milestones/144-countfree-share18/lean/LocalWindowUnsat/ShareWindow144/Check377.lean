import LocalWindowUnsat.ShareWindow144.Data377
import LocalWindowUnsat.ShareWindow144.Data378

/-! Kernel checks of segments 1505-1508 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1505 : check start1505 proof1505 = true := by
  decide +kernel

theorem ok1506 : check start1506 proof1506 = true := by
  decide +kernel

theorem ok1507 : check start1507 proof1507 = true := by
  decide +kernel

theorem ok1508 : andB (check start1508 proof1508) (cpOk (replay start1508 proof1508) start1509) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
