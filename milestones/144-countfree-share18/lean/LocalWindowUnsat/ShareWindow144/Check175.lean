import LocalWindowUnsat.ShareWindow144.Data175
import LocalWindowUnsat.ShareWindow144.Data176

/-! Kernel checks of segments 697-700 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok697 : check start697 proof697 = true := by
  decide +kernel

theorem ok698 : check start698 proof698 = true := by
  decide +kernel

theorem ok699 : check start699 proof699 = true := by
  decide +kernel

theorem ok700 : andB (check start700 proof700) (cpOk (replay start700 proof700) start701) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
