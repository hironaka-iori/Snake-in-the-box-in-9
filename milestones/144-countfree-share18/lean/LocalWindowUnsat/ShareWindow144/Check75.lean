import LocalWindowUnsat.ShareWindow144.Data75
import LocalWindowUnsat.ShareWindow144.Data76

/-! Kernel checks of segments 297-300 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok297 : check start297 proof297 = true := by
  decide +kernel

theorem ok298 : check start298 proof298 = true := by
  decide +kernel

theorem ok299 : check start299 proof299 = true := by
  decide +kernel

theorem ok300 : andB (check start300 proof300) (cpOk (replay start300 proof300) start301) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
