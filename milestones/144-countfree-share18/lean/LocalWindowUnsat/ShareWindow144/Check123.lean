import LocalWindowUnsat.ShareWindow144.Data123
import LocalWindowUnsat.ShareWindow144.Data124

/-! Kernel checks of segments 489-492 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok489 : check start489 proof489 = true := by
  decide +kernel

theorem ok490 : check start490 proof490 = true := by
  decide +kernel

theorem ok491 : check start491 proof491 = true := by
  decide +kernel

theorem ok492 : andB (check start492 proof492) (cpOk (replay start492 proof492) start493) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
