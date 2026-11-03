import LocalWindowUnsat.ShareWindow144.Data128
import LocalWindowUnsat.ShareWindow144.Data129

/-! Kernel checks of segments 509-512 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok509 : check start509 proof509 = true := by
  decide +kernel

theorem ok510 : check start510 proof510 = true := by
  decide +kernel

theorem ok511 : check start511 proof511 = true := by
  decide +kernel

theorem ok512 : andB (check start512 proof512) (cpOk (replay start512 proof512) start513) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
